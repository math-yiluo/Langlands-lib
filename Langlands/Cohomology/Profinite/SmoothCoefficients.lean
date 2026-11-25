import Langlands.Cohomology.Continuous.FiniteQuotientSystem
import Langlands.Representation.Category.Basic
import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Smooth coefficient modules for the cohomology of topological groups

An object `A` of Mathlib's `Rep k G` is a smooth coefficient module when the Library's
`IsSmooth A.ρ` holds: every vector is fixed by an open subgroup. The class `IsSmoothRep A`
records this, so that restriction, subrepresentations, quotients, tensor products and the
other constructions of the cohomology theory carry it by instance search.

The stabilizer of a vector is `Langlands.vectorStabilizer`; a representation is smooth exactly
when all stabilizers are open (`isSmoothRep_iff_isOpen_stabilizer`).
-/

open CategoryTheory Limits Topology MonoidalCategory

namespace Langlands

universe w u v v'

variable {k : Type u} {G : Type v} [CommRing k] [Group G]

section Stabilizer

variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The stabilizer of a vector `v` under a representation `ρ`: the elements `g` with
`ρ g v = v`. -/
def vectorStabilizer (v : V) : Subgroup G where
  carrier := {g | ρ g v = v}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq] at *
    calc ρ a⁻¹ v = ρ a⁻¹ (ρ a v) := by rw [ha]
      _ = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply]

@[simp]
theorem mem_vectorStabilizer (v : V) (g : G) : g ∈ vectorStabilizer ρ v ↔ ρ g v = v :=
  Iff.rfl

theorem vectorStabilizer_zero : vectorStabilizer ρ 0 = ⊤ := by
  ext g
  simp

theorem inf_le_vectorStabilizer_add (a b : V) :
    vectorStabilizer ρ a ⊓ vectorStabilizer ρ b ≤ vectorStabilizer ρ (a + b) := by
  intro g hg
  rw [Subgroup.mem_inf] at hg
  simp only [mem_vectorStabilizer] at *
  rw [map_add, hg.1, hg.2]

theorem vectorStabilizer_le_vectorStabilizer_smul (r : k) (a : V) :
    vectorStabilizer ρ a ≤ vectorStabilizer ρ (r • a) := by
  intro g hg
  simp only [mem_vectorStabilizer] at *
  rw [map_smul, hg]

theorem coe_vectorStabilizer_apply (g : G) (a : V) :
    (vectorStabilizer ρ (ρ g a) : Set G) =
      (fun h => g⁻¹ * h * g) ⁻¹' (vectorStabilizer ρ a : Set G) := by
  ext h
  simp only [SetLike.mem_coe, Set.mem_preimage, mem_vectorStabilizer, map_mul,
    Module.End.mul_apply]
  constructor
  · intro H
    rw [H, Representation.inv_self_apply]
  · intro H
    have := congrArg (ρ g) H
    rwa [Representation.self_inv_apply] at this

theorem vectorStabilizer_eq_top_of_isTrivial [ρ.IsTrivial] (a : V) :
    vectorStabilizer ρ a = ⊤ := by
  ext g
  simp only [mem_vectorStabilizer, Subgroup.mem_top, iff_true]
  rw [Representation.IsTrivial.out g, LinearMap.id_apply]

/-- A vector lies in the invariants of a subgroup exactly when the subgroup fixes it. -/
theorem mem_invariants_comp_subtype_iff (U : Subgroup G) (a : V) :
    a ∈ Representation.invariants (ρ.comp U.subtype) ↔ U ≤ vectorStabilizer ρ a := by
  constructor
  · intro h g hg
    exact h ⟨g, hg⟩
  · intro h g
    exact h g.2

theorem invariants_comp_subtype_antitone {U U' : Subgroup G} (h : U ≤ U') :
    Representation.invariants (ρ.comp U'.subtype) ≤
      Representation.invariants (ρ.comp U.subtype) := by
  intro a ha
  rw [mem_invariants_comp_subtype_iff] at *
  exact h.trans ha

end Stabilizer

theorem vectorStabilizer_le_vectorStabilizer_hom {A B : Rep.{w} k G} (f : A ⟶ B) (a : A) :
    vectorStabilizer A.ρ a ≤ vectorStabilizer B.ρ (f.hom a) := by
  intro g hg
  simp only [mem_vectorStabilizer] at *
  rw [← Rep.hom_comm_apply, hg]

theorem vectorStabilizer_hom_of_injective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) (a : A) :
    vectorStabilizer B.ρ (f.hom a) = vectorStabilizer A.ρ a := by
  ext g
  simp only [mem_vectorStabilizer]
  rw [← Rep.hom_comm_apply]
  exact hf.eq_iff

variable [TopologicalSpace G]

/-- Smoothness of an object of `Rep k G` as a class: the Library's `IsSmooth` of its
representation, i.e. every vector is fixed by an open subgroup. -/
class IsSmoothRep (A : Rep.{w} k G) : Prop where
  isSmooth : IsSmooth A.ρ

theorem isSmoothRep_iff (A : Rep.{w} k G) : IsSmoothRep A ↔ IsSmooth A.ρ :=
  ⟨fun h => h.isSmooth, fun h => ⟨h⟩⟩

theorem isSmoothRep_iff_smoothRepProperty (A : Rep.{w} k G) :
    IsSmoothRep A ↔ smoothRepProperty k G A :=
  isSmoothRep_iff A

/-- The underlying representation of an object of the Library's category of smooth
representations is smooth. -/
instance SmoothRep.isSmoothRep (A : SmoothRep.{u, v, w} k G) : IsSmoothRep A.obj :=
  ⟨A.property⟩

/-- A representation with smoothness as an instance, as an object of `SmoothRep`. -/
abbrev IsSmoothRep.toSmoothRep (A : Rep.{w} k G) [h : IsSmoothRep A] :
    SmoothRep.{u, v, w} k G :=
  ⟨A, h.isSmooth⟩

/-- If every stabilizer is open, the representation is smooth: each stabilizer is itself an
open subgroup fixing its vector. -/
theorem IsSmoothRep.of_isOpen_stabilizer (A : Rep.{w} k G)
    (h : ∀ a : A, IsOpen (vectorStabilizer A.ρ a : Set G)) : IsSmoothRep A :=
  ⟨fun a => ⟨⟨vectorStabilizer A.ρ a, h a⟩, fun g => g.2⟩⟩

/-- In a smooth representation every stabilizer is open. -/
theorem IsSmoothRep.isOpen_stabilizer [ContinuousMul G] (A : Rep.{w} k G) [IsSmoothRep A]
    (a : A) : IsOpen (vectorStabilizer A.ρ a : Set G) := by
  obtain ⟨U, hU⟩ := IsSmoothRep.isSmooth (A := A) a
  exact Subgroup.isOpen_mono (fun g hg => hU ⟨g, hg⟩) U.isOpen

theorem isSmoothRep_iff_isOpen_stabilizer [ContinuousMul G] (A : Rep.{w} k G) :
    IsSmoothRep A ↔ ∀ a : A, IsOpen (vectorStabilizer A.ρ a : Set G) :=
  ⟨fun _ => IsSmoothRep.isOpen_stabilizer A, IsSmoothRep.of_isOpen_stabilizer A⟩

/-- The underlying representation of a discrete module of `Langlands.Continuous` (a discrete
topological module with jointly continuous action) is smooth. -/
instance Continuous.DiscreteModule.isSmoothRep {k G : Type u} [CommRing k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] (A : Continuous.DiscreteModule k G) :
    IsSmoothRep A.toRep := by
  refine IsSmoothRep.of_isOpen_stabilizer _ fun a => ?_
  have hc : _root_.Continuous fun g : G => A.toTopRep.ρ g a :=
    A.continuous_action.comp (continuous_id.prodMk continuous_const)
  exact (isOpen_discrete {a}).preimage hc

section Criteria

instance isSmoothRep_of_discreteTopology [DiscreteTopology G] (A : Rep.{w} k G) :
    IsSmoothRep A :=
  IsSmoothRep.of_isOpen_stabilizer A fun _ => isOpen_discrete _

instance isSmoothRep_of_isTrivial (A : Rep.{w} k G) [A.ρ.IsTrivial] : IsSmoothRep A :=
  IsSmoothRep.of_isOpen_stabilizer A fun a => by
    rw [vectorStabilizer_eq_top_of_isTrivial]; exact isOpen_univ

theorem IsSmoothRep.of_subsingleton (A : Rep.{w} k G) [Subsingleton A] : IsSmoothRep A :=
  IsSmoothRep.of_isOpen_stabilizer A fun a => by
    rw [Subsingleton.elim a 0, vectorStabilizer_zero]; exact isOpen_univ

theorem IsSmoothRep.of_injective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) [IsSmoothRep B] : IsSmoothRep A :=
  ⟨isSmooth_of_injective f.hom hf IsSmoothRep.isSmooth⟩

theorem IsSmoothRep.of_surjective {A B : Rep.{w} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) [IsSmoothRep A] : IsSmoothRep B :=
  ⟨isSmooth_of_surjective f.hom hf IsSmoothRep.isSmooth⟩

theorem IsSmoothRep.of_iso {A B : Rep.{w} k G} (e : A ≅ B) [IsSmoothRep A] :
    IsSmoothRep B :=
  IsSmoothRep.of_surjective e.hom fun b => ⟨e.inv.hom b, Rep.hom_inv_apply (e := e) (x := b)⟩

/-- A representation is smooth if every vector is invariant under some open subgroup. -/
theorem IsSmoothRep.of_forall_exists_mem_invariants (A : Rep.{w} k G)
    (h : ∀ a : A, ∃ U : Subgroup G, IsOpen (U : Set G) ∧
      a ∈ Representation.invariants (A.ρ.comp U.subtype)) :
    IsSmoothRep A :=
  ⟨fun a => by
    obtain ⟨U, hU, ha⟩ := h a
    exact ⟨⟨U, hU⟩, ha⟩⟩

/-- Restriction along a continuous homomorphism preserves smoothness. -/
theorem IsSmoothRep.res {H : Type v'} [Group H] [TopologicalSpace H] {φ : H →* G}
    (hφ : _root_.Continuous φ) (A : Rep.{w} k G) [IsSmoothRep A] :
    IsSmoothRep (Rep.res φ A) :=
  ⟨isSmooth_comp φ hφ IsSmoothRep.isSmooth⟩

/-- Restriction along a bundled continuous homomorphism preserves smoothness. -/
instance isSmoothRep_res {H : Type v'} [Group H] [TopologicalSpace H] (φ : H →ₜ* G)
    (A : Rep.{w} k G) [IsSmoothRep A] : IsSmoothRep (Rep.res (φ : H →* G) A) :=
  IsSmoothRep.res φ.continuous_toFun A

instance isSmoothRep_res_subtype (A : Rep.{w} k G) [IsSmoothRep A] (S : Subgroup G) :
    IsSmoothRep (Rep.res S.subtype A) :=
  IsSmoothRep.res continuous_subtype_val A

end Criteria

section Closure

instance isSmoothRep_subrepresentation (A : Rep.{w} k G) [IsSmoothRep A] (W : Submodule k A)
    (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) : IsSmoothRep (A.subrepresentation W le_comap) :=
  IsSmoothRep.of_injective (Rep.subtype A W le_comap) fun _ _ h => Subtype.ext h

instance isSmoothRep_quotient (A : Rep.{w} k G) [IsSmoothRep A] (W : Submodule k A)
    (le_comap : ∀ g, W ≤ W.comap (A.ρ g)) : IsSmoothRep (A.quotient W le_comap) :=
  IsSmoothRep.of_surjective (Rep.mkQ A W le_comap) (Submodule.mkQ_surjective W)

theorem isSmoothRep_iff_smoothVectors_eq_top (A : Rep.{w} k G) :
    IsSmoothRep A ↔ smoothVectors A.ρ = ⊤ := by
  rw [isSmoothRep_iff, isSmooth_iff_smoothVectors_eq_top]

theorem hom_mem_smoothVectors {A B : Rep.{w} k G} (f : A ⟶ B) {a : A}
    (ha : a ∈ smoothVectors A.ρ) : f.hom a ∈ smoothVectors B.ρ :=
  isSmoothVector_map f.hom ha

theorem mem_smoothVectors_of_isSmoothRep (A : Rep.{w} k G) [IsSmoothRep A] (a : A) :
    a ∈ smoothVectors A.ρ :=
  IsSmoothRep.isSmooth a

instance isSmoothRep_biprod (A B : Rep.{w} k G) [IsSmoothRep A] [IsSmoothRep B] :
    IsSmoothRep (A ⊞ B) := by
  rw [isSmoothRep_iff_smoothVectors_eq_top, Submodule.eq_top_iff']
  intro x
  have hx : x = (biprod.inl : A ⟶ A ⊞ B).hom ((biprod.fst : A ⊞ B ⟶ A).hom x) +
      (biprod.inr : B ⟶ A ⊞ B).hom ((biprod.snd : A ⊞ B ⟶ B).hom x) :=
    calc x = (𝟙 (A ⊞ B) : A ⊞ B ⟶ A ⊞ B).hom x := rfl
      _ = (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr : A ⊞ B ⟶ A ⊞ B).hom x := by
        rw [biprod.total]
      _ = _ := by
        rw [Rep.add_hom, Representation.IntertwiningMap.coe_add, Pi.add_apply]
        rfl
  rw [hx]
  exact Submodule.add_mem _
    (hom_mem_smoothVectors biprod.inl (mem_smoothVectors_of_isSmoothRep A _))
    (hom_mem_smoothVectors biprod.inr (mem_smoothVectors_of_isSmoothRep B _))

instance isSmoothRep_biproduct {J : Type} [Fintype J] (f : J → Rep.{w} k G) [HasBiproduct f]
    [∀ j, IsSmoothRep (f j)] : IsSmoothRep (⨁ f) := by
  rw [isSmoothRep_iff_smoothVectors_eq_top, Submodule.eq_top_iff']
  intro x
  have hx : x = ∑ j, (biproduct.ι f j).hom ((biproduct.π f j).hom x) :=
    calc x = (𝟙 (⨁ f) : ⨁ f ⟶ ⨁ f).hom x := rfl
      _ = (∑ j, biproduct.π f j ≫ biproduct.ι f j : ⨁ f ⟶ ⨁ f).hom x := by
        rw [biproduct.total (f := f)]
      _ = _ := by
        rw [Rep.sum_hom, Representation.IntertwiningMap.sum_apply]
        rfl
  rw [hx]
  exact Submodule.sum_mem _ fun j _ =>
    hom_mem_smoothVectors (biproduct.ι f j) (mem_smoothVectors_of_isSmoothRep (f j) _)

instance isSmoothRep_directSum {ι : Type w} (A : ι → Rep.{w} k G) [∀ i, IsSmoothRep (A i)] :
    IsSmoothRep (Rep.of (Representation.directSum fun i => (A i).ρ)) := by
  classical
  refine ⟨fun x => ?_⟩
  change x ∈ smoothVectors (Rep.of (Representation.directSum fun i => (A i).ρ)).ρ
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun i _ => ?_
  obtain ⟨U, hU⟩ := IsSmoothRep.isSmooth (A := A i) (x i)
  refine ⟨U, fun g => ?_⟩
  change DirectSum.lmap (fun j => (A j).ρ g) (DirectSum.of _ i (x i)) = DirectSum.of _ i (x i)
  rw [DirectSum.lmap_of]
  exact congrArg _ (hU g)

instance isSmoothRep_prod (A B : Rep.{w} k G) [IsSmoothRep A] [IsSmoothRep B] :
    IsSmoothRep (Rep.of (A.ρ.prod B.ρ)) :=
  ⟨fun x => by
    obtain ⟨U, hU⟩ := IsSmoothRep.isSmooth (A := A) x.1
    obtain ⟨U', hU'⟩ := IsSmoothRep.isSmooth (A := B) x.2
    refine ⟨U ⊓ U', fun g => ?_⟩
    exact Prod.ext (hU ⟨g, g.2.1⟩) (hU' ⟨g, g.2.2⟩)⟩

/-- The tensor product of two smooth representations is smooth. -/
instance isSmoothRep_tensor {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]
    (A B : Rep.{u} k G) [IsSmoothRep A] [IsSmoothRep B] :
    IsSmoothRep (A ⊗ B) := by
  rw [isSmoothRep_iff_smoothVectors_eq_top, Submodule.eq_top_iff']
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    obtain ⟨U, hU⟩ := IsSmoothRep.isSmooth (A := A) a
    obtain ⟨U', hU'⟩ := IsSmoothRep.isSmooth (A := B) b
    refine ⟨U ⊓ U', fun g => ?_⟩
    change (A ⊗ B).ρ (g : G) (a ⊗ₜ b) = a ⊗ₜ b
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul]
    rw [show A.ρ (g : G) a = a from hU ⟨g, g.2.1⟩, show B.ρ (g : G) b = b from hU' ⟨g, g.2.2⟩]
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The unit object of the monoidal category `Rep k G` (the trivial module `k`) is smooth. -/
instance isSmoothRep_tensorUnit {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] :
    IsSmoothRep (𝟙_ (Rep.{u} k G)) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun a => by
    have : vectorStabilizer (𝟙_ (Rep.{u} k G)).ρ a = ⊤ := by
      ext g
      simp only [mem_vectorStabilizer, Subgroup.mem_top, iff_true]
      rfl
    rw [this]
    exact isOpen_univ

theorem isSmoothRep_X₁_of_shortExact {S : ShortComplex (Rep.{w} k G)} (hS : S.ShortExact)
    [IsSmoothRep S.X₂] : IsSmoothRep S.X₁ :=
  IsSmoothRep.of_injective S.f ((Rep.mono_iff_injective S.f).1 hS.mono_f)

theorem isSmoothRep_X₃_of_shortExact {S : ShortComplex (Rep.{w} k G)} (hS : S.ShortExact)
    [IsSmoothRep S.X₂] : IsSmoothRep S.X₃ :=
  IsSmoothRep.of_surjective S.g ((Rep.epi_iff_surjective S.g).1 hS.epi_g)

end Closure

section LocallyConstant

variable [IsTopologicalGroup G]

/-- The orbit map `g ↦ ρ g a` of a vector of a smooth representation is locally constant. -/
theorem isLocallyConstant_apply (A : Rep.{w} k G) [IsSmoothRep A] (a : A) :
    IsLocallyConstant fun g : G => A.ρ g a := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro b
  rw [isOpen_iff_forall_mem_open]
  intro g hg
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (vectorStabilizer A.ρ a : Set G), ?_,
    (IsSmoothRep.isOpen_stabilizer A a).preimage (continuous_const.mul continuous_id),
    by simp⟩
  intro h hh
  simp only [Set.mem_preimage, SetLike.mem_coe, mem_vectorStabilizer,
    Set.mem_singleton_iff] at hh hg ⊢
  rw [← hg, show h = g * (g⁻¹ * h) by group, map_mul, Module.End.mul_apply, hh]

end LocallyConstant

section Quotients

variable [IsTopologicalGroup G]

/-- The invariants of a normal subgroup form a smooth representation of the quotient group
(with its quotient topology). -/
instance isSmoothRep_quotientToInvariants (A : Rep.{w} k G) [IsSmoothRep A]
    (N : Subgroup G) [N.Normal] : IsSmoothRep (A.quotientToInvariants N) :=
  IsSmoothRep.of_isOpen_stabilizer _ fun a => by
    rw [← (QuotientGroup.isQuotientMap_mk N).isOpen_preimage]
    have h : (QuotientGroup.mk ⁻¹' (vectorStabilizer (A.quotientToInvariants N).ρ a :
        Set (G ⧸ N))) = (vectorStabilizer A.ρ a.1 : Set G) := by
      ext g
      simp only [Set.mem_preimage, SetLike.mem_coe, mem_vectorStabilizer]
      rw [Subtype.ext_iff]
      rfl
    rw [h]
    exact IsSmoothRep.isOpen_stabilizer A a.1

/-- In a compact group, a representation is smooth exactly when every vector is invariant
under an open normal subgroup. -/
theorem isSmoothRep_iff_forall_exists_openNormalSubgroup [CompactSpace G] (A : Rep.{w} k G) :
    IsSmoothRep A ↔
      ∀ a : A, ∃ U : OpenNormalSubgroup G,
        a ∈ Representation.invariants (A.ρ.comp U.toSubgroup.subtype) := by
  constructor
  · intro _ a
    have ho := IsSmoothRep.isOpen_stabilizer A a
    obtain ⟨U, hU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ ho, ho⟩ (one_mem (vectorStabilizer A.ρ a))
    exact ⟨U, (mem_invariants_comp_subtype_iff A.ρ _ a).2 hU⟩
  · intro h
    exact IsSmoothRep.of_forall_exists_mem_invariants A fun a =>
      let ⟨U, hU⟩ := h a
      ⟨U.toSubgroup, U.isOpen, hU⟩

end Quotients

end Langlands
