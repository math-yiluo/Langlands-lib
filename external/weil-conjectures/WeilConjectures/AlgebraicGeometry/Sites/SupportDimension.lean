/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.Algebra.Category.Grp.Zero

/-!
# Étale sheaves supported in low dimension

Let `B` be a scheme of finite type over a field `K` and `N` a torsion abelian étale sheaf on `B`
whose geometric stalks vanish at every point `y` with `trdeg_K κ(y) > a`. For a closed subset
`Z ⊆ B` with open complement `j_Z : B ∖ Z ⟶ B`, let `N_Z = ker(N ⟶ j_Z* j_Z^* N)` be the
subsheaf of sections supported in `Z`. Then `N` is the filtered union of the `N_Z` over the
closed `Z` of dimension at most `a` (`AlgebraicGeometry.Etale.exists_covering_supportedIn`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PrimeSpectrum

/-- Let `A` be a finitely generated algebra over a field `K` and `φ : A →ₐ[K] L` a morphism to a
field. Then the closed subset `V(ker φ)` of `Spec A` has dimension at most `trdeg_K L`: it is
`Spec (A ⧸ ker φ)`, whose dimension is `trdeg_K (A ⧸ ker φ) ≤ trdeg_K L`. -/
theorem topologicalKrullDim_zeroLocus_le_of_trdeg_le (K : Type*) {A L : Type*} [Field K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [Field L] [Algebra K L]
    (φ : A →ₐ[K] L) (n : ℕ) (h : Algebra.trdeg K L ≤ n) :
    topologicalKrullDim (zeroLocus (RingHom.ker φ : Set A)) ≤ n := by
  set P := RingHom.ker φ
  have hemb := isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk P)
    Ideal.Quotient.mk_surjective
  rw [← Ideal.mk_ker (I := P),
    ← range_comap_of_surjective _ (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    ← hemb.topologicalKrullDim_eq_range,
    topologicalKrullDim_eq_ringKrullDim]
  have : P.IsPrime := RingHom.ker_isPrime φ
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim (A ⧸ P) = m := by
    have h1 := ringKrullDim_ne_top_of_finiteType K (A ⧸ P)
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := A ⧸ P)
    generalize ringKrullDim (A ⧸ P) = d at h0 h1
    induction d using WithBot.recBotCoe with
    | bot => simp at h0
    | coe d =>
      induction d using ENat.recTopCoe with
      | top => exact absurd rfl h1
      | coe n => exact ⟨n, rfl⟩
  have htr := Algebra.trdeg_eq_of_ringKrullDim_eq K (A ⧸ P) hm
  have hle := lift_trdeg_le_of_injective (Ideal.kerLiftAlg φ)
    (Ideal.kerLiftAlg_injective φ)
  rw [htr, Cardinal.lift_natCast] at hle
  have h' := (Cardinal.lift_le.{_}).2 h
  rw [Cardinal.lift_natCast] at h'
  rw [hm]
  exact_mod_cast (Nat.cast_le (α := Cardinal)).1 (hle.trans h')

end PrimeSpectrum

/-- A closed subset `Z` of a quasi-sober `T₀` space has dimension at most `n` if every point of
`Z` is a specialization of a point whose closure has dimension at most `n`. -/
theorem topologicalKrullDim_le_of_forall_exists_specializes {X : Type*} [TopologicalSpace X]
    [QuasiSober X] [T0Space X] {Z : Set X} (hZ : IsClosed Z) (n : WithBot ℕ∞)
    (h : ∀ z ∈ Z, ∃ ξ : X, ξ ⤳ z ∧ topologicalKrullDim (closure ({ξ} : Set X)) ≤ n) :
    topologicalKrullDim Z ≤ n := by
  have := hZ.isClosedEmbedding_subtypeVal.quasiSober
  let := specializationOrder Z
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDim_closure_singleton]
  obtain ⟨ξ, hξz, hξ⟩ := h z.1 z.2
  have hmem (x : closure ({z} : Set Z)) : x.1.1 ∈ closure ({ξ} : Set X) :=
    specializes_iff_mem_closure.1 (hξz.trans
      ((specializes_iff_mem_closure.2 x.2).map continuous_subtype_val))
  let f : closure ({z} : Set Z) → closure ({ξ} : Set X) := fun x ↦ ⟨x.1.1, hmem x⟩
  have hf : Topology.IsInducing f :=
    Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val (g := Subtype.val)
      (Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal :
        Topology.IsInducing fun x : closure ({z} : Set Z) ↦ x.1.1)
  exact hf.topologicalKrullDim_le.trans hξ


namespace AlgebraicGeometry

namespace Scheme

/-- The ring homomorphism `K ⟶ κ(y)` from the ground field `K` of a `K`-scheme `B` (with
structure morphism `b`) to the residue field at a point `y` of `B`. -/
noncomputable def residueFieldHomOfOver {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : K →+* B.residueField y :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ b.appTop ≫ B.presheaf.germ ⊤ y trivial ≫
    B.residue y).hom

/-- The transcendence degree `trdeg_K κ(y)` of the residue field at a point `y` of a `K`-scheme
`B` (with structure morphism `b`). -/
noncomputable def residueFieldTrdeg {K : Type u} [Field K] {B : Scheme.{u}}
    (b : B ⟶ Spec (.of K)) (y : B) : Cardinal.{u} :=
  letI := (residueFieldHomOfOver b y).toAlgebra
  Algebra.trdeg K (B.residueField y)

/-- For a scheme `B` locally of finite type over a field `K`, the closure of a point `y` has
dimension at most `trdeg_K κ(y)`. -/
theorem topologicalKrullDim_closure_singleton_le_of_residueFieldTrdeg_le {K : Type u} [Field K]
    {B : Scheme.{u}} (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] (y : B) (n : ℕ)
    (h : residueFieldTrdeg b y ≤ n) :
    topologicalKrullDim (closure ({y} : Set B)) ≤ n := by
  let C : Set B := closure {y}
  have : QuasiSober C := isClosed_closure.isClosedEmbedding_subtypeVal.quasiSober
  let O (V : B.affineOpens) : TopologicalSpace.Opens C :=
    ⟨Subtype.val ⁻¹' (V : Set B), V.1.isOpen.preimage continuous_subtype_val⟩
  refine topologicalKrullDim_le_of_iSup_eq_top O ?_ n ?_
  · refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      B.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x.1) isOpen_univ
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV⟩, hxV⟩
  rintro ⟨V, hV⟩
  by_cases hy : y ∈ V
  swap
  · have : IsEmpty (O ⟨V, hV⟩) :=
      ⟨fun x ↦ hy ((specializes_iff_mem_closure.2 x.1.2).mem_open V.isOpen x.2)⟩
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds (O ⟨V, hV⟩)) :=
      ⟨fun s ↦ s.isIrreducible.nonempty.elim fun x _ ↦ isEmptyElim x⟩
    rw [topologicalKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  let φK : K →+* Γ(B, V) := (b.appLE ⊤ V (by simp)).hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  let := φK.toAlgebra
  let := (residueFieldHomOfOver b y).toAlgebra
  have : Algebra.FiniteType K Γ(B, V) := by
    have hft : RingHom.FiniteType (b.appLE ⊤ V (by simp)).hom :=
      HasRingHomProperty.appLE (P := @LocallyOfFiniteType) b inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (by simp)
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  let φ : Γ(B, V) →ₐ[K] B.residueField y :=
    { (B.presheaf.germ V y hy ≫ B.residue y).hom with
      commutes' := fun r ↦ by
        simp only [RingHom.algebraMap_toAlgebra, φK, residueFieldHomOfOver, Scheme.Hom.appLE]
        simp }
  have hP : RingHom.ker φ = (hV.primeIdealOf ⟨y, hy⟩).asIdeal := by
    rw [hV.primeIdealOf_eq_map_closedPoint, Spec.map_apply]
    ext a
    simp only [φ, Scheme.residue, IsLocalRing.closedPoint]
    exact IsLocalRing.residue_eq_zero_iff _
  have hmem (p : PrimeSpectrum Γ(B, V)) :
      p ∈ PrimeSpectrum.zeroLocus (RingHom.ker φ : Set Γ(B, V)) ↔ hV.fromSpec p ∈ C := by
    rw [hP, ← PrimeSpectrum.closure_singleton, ← specializes_iff_mem_closure,
      ← hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff, hV.fromSpec_primeIdealOf,
      specializes_iff_mem_closure]
  have hf : Topology.IsEmbedding fun x : O ⟨V, hV⟩ ↦ (x.1.1 : B) :=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hg : Topology.IsEmbedding fun x : PrimeSpectrum.zeroLocus (RingHom.ker φ : Set Γ(B, V)) ↦
      hV.fromSpec x.1 :=
    hV.fromSpec.isOpenEmbedding.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hrange : Set.range (fun x : O ⟨V, hV⟩ ↦ (x.1.1 : B)) =
      Set.range fun x : PrimeSpectrum.zeroLocus (RingHom.ker φ : Set Γ(B, V)) ↦
        hV.fromSpec x.1 := by
    ext x
    constructor
    · rintro ⟨⟨⟨x, hxC⟩, hxV⟩, rfl⟩
      obtain ⟨p, rfl⟩ : x ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
      exact ⟨⟨p, (hmem p).2 hxC⟩, rfl⟩
    · rintro ⟨⟨p, hp⟩, rfl⟩
      refine ⟨⟨⟨hV.fromSpec p, (hmem p).1 hp⟩, ?_⟩, rfl⟩
      exact (hV.range_fromSpec ▸ Set.mem_range_self p : hV.fromSpec p ∈ (V : Set B))
  rw [hf.topologicalKrullDim_eq_range, hrange, ← hg.topologicalKrullDim_eq_range]
  exact PrimeSpectrum.topologicalKrullDim_zeroLocus_le_of_trdeg_le K φ n h


end Scheme

namespace Etale

variable {B : Scheme.{u}}

/-- The subsheaf `N_Z = ker(N ⟶ j_* j^* N)` of sections of `N` supported in the closed
complement of an open `U` of `B`, where `j : U ⟶ B` is the inclusion. -/
noncomputable def supportedIn (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  kernel ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N)

/-- The inclusion `N_Z ⟶ N` of the sections supported in the complement of `U`. -/
noncomputable def supportedInι (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    (U : B.Opens) : supportedIn N U ⟶ N :=
  kernel.ι _

/-- A section of an abelian étale sheaf `N` on `B` vanishes étale locally around every point `v`
lying over a point `y` such that `N` has zero geometric stalk at all geometric points over
`y`. -/
lemma mem_vanishingLocus_of_isZero_upperStar
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1})
    {V : B.Etale} (s : N.obj.obj (Opposite.op V)) (v : V.left)
    (h : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      s (IsLocalRing.closedPoint Ω) = V.hom v → IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N)) :
    v ∈ vanishingLocus N s := by
  let Ω := AlgebraicClosure (V.left.residueField v)
  let φ : Spec (.of Ω) ⟶ V.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (V.left.residueField v) Ω)) ≫
      V.left.fromSpecResidueField v
  have hφ : φ (IsLocalRing.closedPoint Ω) = v := by
    rw [Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hZ := h Ω (φ ≫ V.hom) ((Scheme.Hom.comp_apply _ _ _).trans (congrArg V.hom hφ))
  let T : (Spec (.of Ω)).Etale :=
    MorphismProperty.Over.mk ⊤ (𝟙 _) (MorphismProperty.id_mem _ _)
  have hsub := range_subset_vanishingLocus_of_pullSection_eq_zero (φ ≫ V.hom) N (V := T) φ
    (Category.id_comp _).symm s (by
      have := ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (Opposite.op T)).map_isZero hZ)
      exact (AddCommGrpCat.isZero_iff_subsingleton.1 this).elim _ _)
  exact hsub ⟨IsLocalRing.closedPoint Ω, hφ⟩

/-- Let `U ⊆ B` be open with inclusion `j`. A section `s` of an abelian étale sheaf `N` over `W`
which vanishes étale locally around every point of `W` lying over `U` is killed by the unit
`N ⟶ j_* j^* N`. -/
lemma unit_app_eq_zero_of_forall_mem_vanishingLocus
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : B.Opens) {W : B.Etale}
    (s : N.obj.obj (Opposite.op W)) (h : ∀ w : W.left, W.hom w ∈ U → w ∈ vanishingLocus N s) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom.app
      (Opposite.op W) s = 0 := by
  refine eq_zero_of_forall_mem_vanishingLocus (F := (U.ι)^*[AddCommGrpCat.{u + 1}].obj N)
    (U := (MorphismProperty.Over.pullback @Etale ⊤ U.ι).obj W) fun p ↦ ?_
  have hp : W.hom (pullback.fst W.hom U.ι p) = U.ι (pullback.snd W.hom U.ι p) := by
    simpa using congrArg (fun f : pullback W.hom U.ι ⟶ B ↦ f p)
      (pullback.condition (f := W.hom) (g := U.ι))
  obtain ⟨W', g, ⟨w', hw'⟩, hs⟩ :=
    h (pullback.fst W.hom U.ι p) (hp ▸ (pullback.snd W.hom U.ι p).2)
  have hw : W'.hom w' = U.ι (pullback.snd W.hom U.ι p) := by
    rw [← hp, ← hw']
    exact ((Scheme.Hom.comp_apply _ _ _).symm.trans
      (congrArg (fun f : W'.left ⟶ B ↦ f w') (MorphismProperty.Over.w g))).symm
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback w' _ hw
  refine ⟨_, (MorphismProperty.Over.pullback @Etale ⊤ U.ι).map g, ⟨z, ?_⟩, ?_⟩
  · apply (pullback.fst W.hom U.ι).isOpenEmbedding.injective
    have := congrArg (fun f : pullback W'.hom U.ι ⟶ W.left ↦ f z)
      (pullback.lift_fst (pullback.fst W'.hom U.ι ≫ g.left) (pullback.snd W'.hom U.ι)
        (by rw [Category.assoc, MorphismProperty.Over.w g, pullback.condition]))
    simp only [Scheme.Hom.comp_apply] at this
    rw [overPullback_map_left]
    exact this.trans ((congrArg g.left hz₁).trans hw')
  · have := NatTrans.naturality_apply
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} U.ι).unit.app N).hom g.op s
    simp only [Functor.id_obj, hs, map_zero] at this
    exact this.symm

/-- Let `B` be locally of finite type over a field `K` and `s` a section of an abelian étale
sheaf `N` over a quasi-compact étale `W ⟶ B`, such that every point of `W` near which `s` does
not vanish lies over a point `y` with `trdeg_K κ(y) ≤ a`. Then `s` lies in `N_Z` for a closed
`Z ⊆ B` of dimension at most `a`: the closure of the image of the support of `s`. -/
lemma exists_supportedIn_of_forall_residueFieldTrdeg_le {K : Type u} [Field K]
    (b : B ⟶ Spec (.of K)) [LocallyOfFiniteType b] (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) {W : B.Etale} [CompactSpace W.left]
    (s : N.obj.obj (Opposite.op W))
    (hs : ∀ w : W.left, w ∉ vanishingLocus N s → Scheme.residueFieldTrdeg b (W.hom w) ≤ a) :
    ∃ (U : B.Opens) (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
      (t : (supportedIn N U).obj.obj (Opposite.op W)), (supportedInι N U).hom.app _ t = s := by
  have : Etale W.hom := W.prop
  have : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian (W.hom ≫ b)
  have : IsNoetherian W.left := ⟨⟩
  obtain ⟨G, hGf, hGS, hG⟩ :=
    (isOpen_vanishingLocus s).isClosed_compl.exists_finite_forall_exists_specializes
  let Z : Set B := ⋃ ξ ∈ G, closure {W.hom ξ}
  have hZ : IsClosed Z := hGf.isClosed_biUnion fun _ _ ↦ isClosed_closure
  have hU : ∀ w : W.left, W.hom w ∈ (⟨Zᶜ, hZ.isOpen_compl⟩ : B.Opens) →
      w ∈ vanishingLocus N s := fun w hw ↦ by
    by_contra hv
    obtain ⟨ξ, hξG, hξw⟩ := hG w hv
    exact hw (Set.mem_iUnion₂.2
      ⟨ξ, hξG, specializes_iff_mem_closure.1 (hξw.map W.hom.continuous)⟩)
  obtain ⟨t, ht⟩ := Scheme.exists_kernel_ι_app_eq_ab _ s
    (unit_app_eq_zero_of_forall_mem_vanishingLocus N _ s hU)
  refine ⟨⟨Zᶜ, hZ.isOpen_compl⟩, ?_, t, ht⟩
  rw [TopologicalSpace.Opens.coe_mk, compl_compl]
  refine topologicalKrullDim_le_of_forall_exists_specializes hZ _ fun z hz ↦ ?_
  obtain ⟨ξ, hξG, hzξ⟩ := Set.mem_iUnion₂.1 hz
  exact ⟨W.hom ξ, specializes_iff_mem_closure.2 hzξ,
    Scheme.topologicalKrullDim_closure_singleton_le_of_residueFieldTrdeg_le b _ a
      (hs ξ (hGS hξG))⟩

/-- **A sheaf supported in low dimension is a filtered union.** Let `B` be a scheme of finite
type over a field `K` (structure morphism `b`), `a ≥ 0`, and `N` a torsion abelian étale sheaf
on `B` with zero geometric stalk at every point `y` with `trdeg_K κ(y) > a`: for every
separably closed field `Ω` and every geometric point `s: Spec Ω ⟶ B` lying over such a `y`,
`s^* N = 0`. For a closed `Z ⊆ B` with complement `j_Z: B ∖ Z ⟶ B` let
`N_Z = ker(N ⟶ j_Z* j_Z^* N)`. Then `N` is the union of the subsheaves `N_Z` over the closed `Z`
of dimension at most `a`: every section of `N` lies, locally on an étale covering, in some
`N_Z`. -/
theorem exists_covering_supportedIn {K : Type u} [Field K] (b : B ⟶ Spec (.of K))
    [LocallyOfFiniteType b] [QuasiCompact b] (a : ℕ)
    (N : Sheaf B.smallEtaleTopology AddCommGrpCat.{u + 1}) (_hN : N.IsTorsion)
    (hstalk : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ B),
      (a : Cardinal.{u}) < Scheme.residueFieldTrdeg b (s (IsLocalRing.closedPoint Ω)) →
        IsZero ((s)^*[AddCommGrpCat.{u + 1}].obj N)) :
    ∀ (V : B.Etale) (s : N.obj.obj (Opposite.op V)), ∃ R ∈ B.smallEtaleTopology V,
      ∀ ⦃W : B.Etale⦄ (g : W ⟶ V), R g → ∃ (U : B.Opens)
        (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
        (t : (supportedIn N U).obj.obj (Opposite.op W)),
          (supportedInι N U).hom.app _ t = N.obj.map g.op s := by
  intro V s
  let R : Sieve V :=
    { arrows := fun W g ↦ ∃ (U : B.Opens) (_ : topologicalKrullDim ((U : Set B)ᶜ : Set B) ≤ a)
        (t : (supportedIn N U).obj.obj (Opposite.op W)),
          (supportedInι N U).hom.app _ t = N.obj.map g.op s
      downward_closed := by
        rintro W W' g ⟨U, hU, t, ht⟩ f
        refine ⟨U, hU, (supportedIn N U).obj.map f.op t, ?_⟩
        rw [NatTrans.naturality_apply, ht, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
          ← op_comp] }
  refine ⟨R, ?_, fun W g hg ↦ hg⟩
  rw [Scheme.mem_smallEtaleTopology_iff]
  intro x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    V.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Etale V.hom := V.prop
  let Wₑ : B.Etale := MorphismProperty.Over.mk ⊤ (Scheme.Opens.ι (X := V.left) W ≫ V.hom)
    inferInstance
  let g : Wₑ ⟶ V := MorphismProperty.Over.homMk (Scheme.Opens.ι (X := V.left) W) rfl
  refine ⟨Wₑ, g, ?_, ⟨⟨x, hxW⟩, rfl⟩⟩
  have : IsAffine W := hW
  have : CompactSpace Wₑ.left := inferInstanceAs (CompactSpace W)
  exact exists_supportedIn_of_forall_residueFieldTrdeg_le b a N (N.obj.map g.op s)
    fun w hw ↦ not_lt.1 fun hlt ↦ hw (mem_vanishingLocus_of_isZero_upperStar N _ w
      fun Ω _ _ t ht ↦ hstalk Ω t (ht ▸ hlt))

end Etale

end AlgebraicGeometry
