/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.GenericRestriction
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantSheafSections
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
public import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Sheaves on a field split by a Galois extension

Let `F` be a field and `L / F` a finite Galois extension. An abelian étale sheaf `N` on `Spec F`
is *split by* `L` (`AlgebraicGeometry.Scheme.IsSplitBy`) if it becomes constant over `Spec L`:
restriction from `Spec L` to every one-point étale scheme over `Spec L` is bijective.

Two morphisms from a one-point étale `F`-scheme to `Spec L` differ by an element of
`Gal(L / F)`, so the global sections of `N` are the Galois invariant sections over `Spec L`
(Galois descent). If `Gal(L / F)` is an `ℓ`-group and the sections of `N` over `Spec L` form a
finite `ℓ`-group, then the number of invariant sections is divisible by `ℓ`, so `N` has a global
section of order `ℓ`, that is a monomorphism `ℤ/ℓ ⟶ N`, whose cokernel is again split by `L`, with
fewer sections over `Spec L`. By induction `N` is filtered by constant sheaves `ℤ/ℓ`
(`AlgebraicGeometry.Scheme.IsSplitBy.induction`). This is the sheaf form of the Sylow reduction of
a finite `ℓ`-primary Galois module.

## Main statements

- `AlgebraicGeometry.Scheme.exists_map_eq_of_forall_map_etaleSpecMap_eq`: Galois descent of
  sections.
- `AlgebraicGeometry.Scheme.IsSplitBy.induction`: the filtration by constant sheaves `ℤ/ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

open GaloisCech

variable {F : Type u} [Field F]
  (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})

/-- Restriction to a nonempty étale scheme over a one-point étale scheme over a field is
injective. -/
lemma injective_map_of_subsingleton {Z Z' : (Spec (.of F)).Etale} [Subsingleton Z.left]
    [Nonempty Z'.left] (g : Z' ⟶ Z) : Function.Injective (N.obj.map g.op) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  refine (isSheafFor_ofArrows N (fun _ : Unit ↦ g) ?_).isSeparatedFor.ext fun _ _ ⟨_⟩ ↦ ?_
  · refine Set.eq_univ_of_forall fun z ↦ Set.mem_iUnion.2 ⟨(), Classical.arbitrary _, ?_⟩
    exact Subsingleton.elim _ _
  · exact show N.obj.map g.op x = N.obj.map g.op 0 from hx.trans (map_zero _).symm

variable {N} (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]

/-- **Two morphisms from a one-point scheme to `Spec L` differ by a Galois automorphism** when
`L / F` is normal. -/
lemma exists_eq_comp_etaleSpecMap [Normal F L] {Z : (Spec (.of F)).Etale} [Subsingleton Z.left]
    [Nonempty Z.left] (p q : Z ⟶ etaleSpec F L) :
    ∃ σ : L ≃ₐ[F] L, q = p ≫ etaleSpecMap σ.toAlgHom := by
  let := (isField_of_etale_of_subsingleton Z).toField
  let E := Γ(Z.left, ⊤)
  let : Algebra F E := (toRing Z.hom).toAlgebra
  have hp (r : Z ⟶ etaleSpec F L) : (toRing r.left).comp (algebraMap F L) = algebraMap F E := by
    exact (toRing_comp_specMap r.left (CommRingCat.ofHom (algebraMap F L))).symm.trans
      (congrArg toRing (MorphismProperty.Over.w r))
  let φ (r : Z ⟶ etaleSpec F L) : L →ₐ[F] E :=
    { toRingHom := toRing r.left
      commutes' x := congrArg (fun ψ : F →+* E ↦ ψ x) (hp r) }
  let : Algebra L E := (φ p).toRingHom.toAlgebra
  have : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun x ↦ ((φ p).commutes x).symm
  let σ := (φ q).restrictNormal' L
  refine ⟨σ, ?_⟩
  refine MorphismProperty.Over.Hom.ext (eq_of_toRing_eq ?_)
  change toRing q.left = toRing (p.left ≫ Spec.map _)
  rw [toRing_comp_specMap]
  ext x
  exact ((φ q).restrictNormal_commutes L x).symm

variable {L}

section Points

variable (V : (Spec (.of F)).Etale)

instance : DiscreteTopology V.left := discreteTopology_of_etale_of_unique V

/-- The open point `{v}` of an étale scheme `V` over a field. -/
noncomputable def pointOpens (v : V.left) : V.left.Opens := ⟨{v}, isOpen_discrete _⟩

/-- The open point `{v}` of an étale scheme `V` over a field, as an étale scheme. -/
noncomputable abbrev pointObj (v : V.left) : (Spec (.of F)).Etale :=
  Etale.ofOpens V (pointOpens V v)

/-- The inclusion of the open point `{v}`. -/
noncomputable abbrev pointι (v : V.left) : pointObj V v ⟶ V :=
  Etale.ofOpensι V (pointOpens V v)

instance (v : V.left) : Subsingleton (pointObj V v).left :=
  inferInstanceAs (Subsingleton ({v} : Set V.left))

instance (v : V.left) : Nonempty (pointObj V v).left :=
  ⟨⟨v, rfl⟩⟩

lemma iUnion_range_pointι : ⋃ v, Set.range (pointι V v).left = Set.univ :=
  Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ⟨v, ⟨⟨v, rfl⟩, rfl⟩⟩

variable {V} (N) in
/-- Sections over an étale scheme over a field are determined by their restrictions to the open
points. -/
lemma ext_of_pointι {x y : N.obj.obj (op V)}
    (h : ∀ v, N.obj.map (pointι V v).op x = N.obj.map (pointι V v).op y) : x = y :=
  (isSheafFor_ofArrows N (pointι V) (iUnion_range_pointι V)).isSeparatedFor.ext
    fun _ _ ⟨v⟩ ↦ h v

end Points

/-- **Galois descent, compatibility.** A section over `Spec L`, for `L / F` Galois, which is
invariant under `Gal(L / F)` has the same pullback along any two morphisms to `Spec L`. -/
lemma map_eq_map_of_forall_map_etaleSpecMap_eq [IsGalois F L]
    (x : N.obj.obj (op (etaleSpec F L)))
    (hx : ∀ σ : L ≃ₐ[F] L, N.obj.map (etaleSpecMap σ.toAlgHom).op x = x)
    {Z : (Spec (.of F)).Etale} (g₁ g₂ : Z ⟶ etaleSpec F L) :
    N.obj.map g₁.op x = N.obj.map g₂.op x := by
  refine ext_of_pointι N fun v ↦ ?_
  obtain ⟨σ, hσ⟩ := exists_eq_comp_etaleSpecMap L (pointι Z v ≫ g₁) (pointι Z v ≫ g₂)
  refine (FieldTrace.map_map_apply N.obj _ _ x).trans ?_
  rw [FieldTrace.map_map_apply N.obj (pointι Z v) g₂, hσ,
    ← FieldTrace.map_map_apply N.obj (pointι Z v ≫ g₁), hx]

/-- The morphism `Spec L ⟶ Spec F` to the terminal object. -/
noncomputable abbrev etaleSpecToTerminal (L : Type u) [Field L] [Algebra F L]
    [Algebra.Etale F L] : etaleSpec F L ⟶ etalePoint F :=
  isTerminalEtalePoint.from _

/-- **Galois descent.** A section over `Spec L`, for `L / F` Galois, which is invariant under
`Gal(L / F)` comes from a global section. -/
lemma exists_map_eq_of_forall_map_etaleSpecMap_eq [IsGalois F L]
    (x : N.obj.obj (op (etaleSpec F L)))
    (hx : ∀ σ : L ≃ₐ[F] L, N.obj.map (etaleSpecMap σ.toAlgHom).op x = x) :
    ∃ y, N.obj.map (etaleSpecToTerminal L).op y = x := by
  have hcov : Sieve.ofArrows _ (fun _ : Unit ↦ etaleSpecToTerminal (F := F) L) ∈
      (Spec (.of F)).smallEtaleTopology _ := by
    rw [ofArrows_mem_smallEtaleTopology_iff]
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨(), (default : Spec (.of L)), @Subsingleton.elim (Spec (.of F)) _ _ _⟩
  have hsheaf : Presieve.IsSheafFor (N.obj ⋙ CategoryTheory.forget _)
      (Presieve.singleton (etaleSpecToTerminal (F := F) L)) := by
    have := (isSheaf_iff_isSheaf_of_type _ _).mp
      (Presheaf.isSheaf_comp_of_isSheaf _ N.obj (CategoryTheory.forget AddCommGrpCat) N.property)
    rw [← Presieve.ofArrows_pUnit.{0}, Presieve.isSheafFor_iff_generate]
    exact this _ hcov
  obtain ⟨y, hy, -⟩ := Presieve.isSheafFor_singleton.mp hsheaf x
    (fun g₁ g₂ _ ↦ map_eq_map_of_forall_map_etaleSpecMap_eq x hx g₁ g₂)
  exact ⟨y, hy⟩

section Constant

variable (B : AddCommGrpCat.{u + 1})

/-- Over a one-point étale scheme over a field, the sections of a constant sheaf are the constant
value. -/
lemma bijective_toSheafify_app_of_subsingleton (W : (Spec (.of F)).Etale)
    [Subsingleton W.left] [Nonempty W.left] :
    Function.Bijective ((CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
      ((Functor.const _).obj B)).app (op W)) := by
  have := isIso_constantSheafToPointFunctionSheaf (X := Spec (.of F)) (M := B)
    (fun V ↦ discreteTopology_of_etale_of_unique V)
  have hψ : Function.Bijective
      (((Spec (.of F)).constantSheafToPointFunctionSheaf B).hom.app (op W)) :=
    (ConcreteCategory.isIso_iff_bijective _).1 (inferInstanceAs (IsIso
      (((sheafToPresheaf _ _).map ((Spec (.of F)).constantSheafToPointFunctionSheaf B)).app
        (op W))))
  have hc : Function.Bijective (fun (m : B) (_ : W.left) ↦ m) :=
    ⟨fun m m' h ↦ congrFun h (Classical.arbitrary _),
      fun D ↦ ⟨D (Classical.arbitrary _), funext fun w ↦ congrArg D (Subsingleton.elim _ _)⟩⟩
  have h : (((Spec (.of F)).constantSheafToPointFunctionSheaf B).hom.app (op W)) ∘
      ((CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
        ((Functor.const _).obj B)).app (op W)) = fun (m : B) (_ : W.left) ↦ m :=
    funext fun m ↦ constantSheafToPointFunctionSheaf_app_toSheafify _ B W m
  rw [← h] at hc
  exact (Function.Bijective.of_comp_iff' hψ _).1 hc

end Constant

section Split

variable (N L)

/-- A sheaf `N` on `Spec F` *is split by* `L` if it becomes constant over `Spec L`: restriction
from `Spec L` to every one-point étale scheme over `Spec L` is bijective. -/
def IsSplitBy : Prop :=
  ∀ (Z : (Spec (.of F)).Etale) [Subsingleton Z.left] [Nonempty Z.left] (t : Z ⟶ etaleSpec F L),
    Function.Bijective (N.obj.map t.op)

variable {N L}

instance : Subsingleton (etalePoint F : (Spec (.of F)).Etale).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum F))

instance : Nonempty (etalePoint F : (Spec (.of F)).Etale).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum F))

instance : Subsingleton (etaleSpec F L).left :=
  inferInstanceAs (Subsingleton (PrimeSpectrum L))

instance : Nonempty (etaleSpec F L).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum L))

variable (ℓ : ℕ) {z : N.obj.obj (op (etalePoint F))} (hz : (ℓ : ℤ) • z = 0)

/-- The morphism `ℤ/ℓ → N(Spec F)` sending `1` to `z`. -/
noncomputable def zmodHom :
    AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)) ⟶ N.obj.obj (op (etalePoint F)) :=
  AddCommGrpCat.ofHom ((ZMod.lift ℓ ⟨zmultiplesHom _ z, by simpa using hz⟩).comp
    AddEquiv.ulift.toAddMonoidHom)

lemma zmodHom_apply (n : ℤ) : (zmodHom ℓ hz).hom (ULift.up (n : ZMod ℓ)) = n • z := by
  change ZMod.lift ℓ ⟨zmultiplesHom _ z, by simpa using hz⟩ (n : ZMod ℓ) = _
  rw [ZMod.lift_coe]
  rfl

lemma range_zmodHom : AddMonoidHom.range (zmodHom ℓ hz).hom = AddSubgroup.zmultiples z := by
  ext x
  constructor
  · rintro ⟨⟨c⟩, rfl⟩
    obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
    exact ⟨n, (zmodHom_apply ℓ hz n).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨⟨(n : ZMod ℓ)⟩, zmodHom_apply ℓ hz n⟩


lemma injective_zmodHom (hℓ : addOrderOf z = ℓ) : Function.Injective (zmodHom ℓ hz).hom := by
  refine (injective_iff_map_eq_zero _).2 fun ⟨c⟩ hc ↦ ?_
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective c
  have : n • z = 0 := (zmodHom_apply ℓ hz n).symm.trans hc
  have hd := addOrderOf_dvd_iff_zsmul_eq_zero.2 this
  rw [hℓ] at hd
  exact ULift.ext ((ZMod.intCast_zmod_eq_zero_iff_dvd n ℓ).2 hd)

/-- The morphism `ℤ/ℓ ⟶ N` of sheaves sending `1` to the global section `z`. -/
noncomputable def constantZModHom : (Spec (.of F)).constantZMod ℓ ⟶ N :=
  ((constantSheafAdj (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}
    GaloisCech.isTerminal).homEquiv _ _).symm
    (zmodHom ℓ hz)

lemma constantZModHom_app_toSheafify (W : (Spec (.of F)).Etale) (b : ULift.{u + 1} (ZMod ℓ)) :
    (constantZModHom ℓ hz).hom.app (op W) ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op W) b) =
      N.obj.map (isTerminalEtalePoint.from W).op (zmodHom ℓ hz b) := by
  have h := constantSheafAdj_homEquiv_apply (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}
    GaloisCech.isTerminal
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) N (constantZModHom ℓ hz)
  rw [constantZModHom, Equiv.apply_symm_apply] at h
  have h₁ := NatTrans.naturality_apply (CategoryTheory.toSheafify (Spec (.of F)).smallEtaleTopology
    ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ)))))
      (isTerminalEtalePoint.from W).op b
  refine (congrArg _ h₁).trans ?_
  exact (NatTrans.naturality_apply (constantZModHom ℓ hz).hom _ _).trans
    (congrArg _ (ConcreteCategory.congr_hom h b).symm)


lemma exists_toSheafify_app_eq (W : (Spec (.of F)).Etale) [Subsingleton W.left]
    [Nonempty W.left] (c : ((Spec (.of F)).constantZMod ℓ).obj.obj (op W)) :
    ∃ b, (CategoryTheory.toSheafify _ ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op W) b = c :=
  (bijective_toSheafify_app_of_subsingleton _ W).2 c

/-- The morphism `ℤ/ℓ ⟶ N` attached to a global section of order `ℓ` is a monomorphism. -/
lemma mono_constantZModHom (hℓ : addOrderOf z = ℓ) : Mono (constantZModHom ℓ hz) := by
  have (V : (Spec (.of F)).Etaleᵒᵖ) : Mono ((constantZModHom ℓ hz).hom.app V) := by
    refine (AddCommGrpCat.mono_iff_injective _).2 ((injective_iff_map_eq_zero _).2 fun s hs ↦ ?_)
    refine ext_of_pointι _ fun v ↦ ?_
    obtain ⟨b, hb⟩ := exists_toSheafify_app_eq ℓ (pointObj V.unop v)
      (((Spec (.of F)).constantZMod ℓ).obj.map (pointι V.unop v).op s)
    have h := NatTrans.naturality_apply (constantZModHom ℓ hz).hom (pointι V.unop v).op s
    rw [hs, map_zero, ← hb, constantZModHom_app_toSheafify] at h
    have hb0 : b = 0 := injective_zmodHom ℓ hz hℓ
      ((injective_map_of_subsingleton N _ (h.trans (map_zero _).symm)).trans (map_zero _).symm)
    rw [map_zero, ← hb, hb0, map_zero]
  have : Mono (constantZModHom ℓ hz).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-- The constant sheaf `ℤ/ℓ` is split by every `L`. -/
lemma isSplitBy_constantZMod : IsSplitBy ((Spec (.of F)).constantZMod ℓ) L := by
  intro Z _ _ t
  have h := (bijective_toSheafify_app_of_subsingleton
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) (etaleSpec F L))
  have h' := (bijective_toSheafify_app_of_subsingleton
    (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))) Z)
  have hc : (((Spec (.of F)).constantZMod ℓ).obj.map t.op) ∘ ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app
        (op (etaleSpec F L))) = ((CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app (op Z)) :=
    funext fun b ↦ (NatTrans.naturality_apply (CategoryTheory.toSheafify _
      ((Functor.const _).obj (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))) t.op b).symm
  exact (Function.Bijective.of_comp_iff _ h).1 (hc ▸ h')

section Cokernel

variable {A : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}} (f : A ⟶ N) [Mono f]

/-- Exactness of `A ⟶ N ⟶ coker f` on sections, for a monomorphism `f`. -/
lemma exists_app_eq_of_cokernel_π_app_eq_zero {W : (Spec (.of F)).Etale} (n : N.obj.obj (op W))
    (hn : (cokernel.π f).hom.app (op W) n = 0) : ∃ a, f.hom.app (op W) a = n := by
  obtain ⟨t, ht⟩ := Etale.exists_kernel_ι_app_eq (cokernel.π f) n hn
  have hl := Abelian.monoIsKernelOfCokernel _ (colimit.isColimit (parallelPair f 0))
  let k := hl.lift (KernelFork.ofι (kernel.ι (cokernel.π f)) (kernel.condition _))
  have hk : k ≫ f = kernel.ι (cokernel.π f) :=
    hl.fac (KernelFork.ofι (kernel.ι (cokernel.π f)) (kernel.condition _)) WalkingParallelPair.zero
  exact ⟨k.hom.app (op W) t, (ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op W)) hk) t).trans ht⟩

omit [Mono f] in
/-- Over a one-point scheme over `Spec L`, every section of `coker f` lifts to `N`, when `N` is
split by `L`. -/
lemma surjective_cokernel_π_app (hN : IsSplitBy N L) (W : (Spec (.of F)).Etale)
    [Subsingleton W.left] [Nonempty W.left] (t : W ⟶ etaleSpec F L) :
    Function.Surjective ((cokernel.π f).hom.app (op W)) := by
  intro q
  have : Sheaf.IsLocallySurjective (cokernel.π f) :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := cokernel.π f)).2 inferInstance
  obtain ⟨W', g, w', hg, -⟩ := exists_of_mem_smallEtaleTopology
    (Presheaf.imageSieve_mem (Spec (.of F)).smallEtaleTopology (cokernel.π f).hom q)
    (Classical.arbitrary W.left)
  let g'' := pointι W' w' ≫ g
  obtain ⟨n, hn⟩ := (Presheaf.imageSieve _ _).downward_closed hg (pointι W' w')
  obtain ⟨m, rfl⟩ := (hN _ (g'' ≫ t)).2 n
  refine ⟨N.obj.map t.op m, injective_map_of_subsingleton _ g'' ?_⟩
  rw [← NatTrans.naturality_apply, FieldTrace.map_map_apply]
  exact hn

/-- **The cokernel of a monomorphism of split sheaves is split.** -/
lemma isSplitBy_cokernel (hA : IsSplitBy A L) (hN : IsSplitBy N L) :
    IsSplitBy (cokernel f) L := by
  intro Z _ _ t
  have hsL := surjective_cokernel_π_app f hN (etaleSpec F L) (𝟙 _)
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_, fun q ↦ ?_⟩
  · obtain ⟨m, rfl⟩ := hsL q
    rw [← NatTrans.naturality_apply] at hq
    obtain ⟨a, ha⟩ := exists_app_eq_of_cokernel_π_app_eq_zero f _ hq
    obtain ⟨a', rfl⟩ := (hA Z t).2 a
    rw [NatTrans.naturality_apply] at ha
    rw [← (hN Z t).1 ha]
    exact ConcreteCategory.congr_hom
      (congrArg (fun φ ↦ φ.hom.app (op (etaleSpec F L))) (cokernel.condition f)) a'
  · obtain ⟨n, rfl⟩ := surjective_cokernel_π_app f hN Z t q
    obtain ⟨m, rfl⟩ := (hN Z t).2 n
    exact ⟨_, (NatTrans.naturality_apply (cokernel.π f).hom t.op m).symm⟩

omit [Mono f] in
/-- Passing to the cokernel of a nonzero monomorphism of split sheaves decreases the size of
the sections over `Spec L`. -/
lemma card_cokernel_lt [Finite (N.obj.obj (op (etaleSpec F L)))] (hN : IsSplitBy N L)
    (a : A.obj.obj (op (etaleSpec F L))) (ha : f.hom.app _ a ≠ 0) :
    Nat.card ((cokernel f).obj.obj (op (etaleSpec F L))) <
      Nat.card (N.obj.obj (op (etaleSpec F L))) := by
  have hs := surjective_cokernel_π_app f hN (etaleSpec F L) (𝟙 _)
  have := Finite.of_surjective _ hs
  have := Fintype.ofFinite (N.obj.obj (op (etaleSpec F L)))
  have := Fintype.ofFinite ((cokernel f).obj.obj (op (etaleSpec F L)))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  refine Fintype.card_lt_of_surjective_not_injective _ hs fun hi ↦ ha (hi ?_)
  rw [map_zero]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ ↦ φ.hom.app (op (etaleSpec F L))) (cokernel.condition f)) a

end Cokernel

variable (L) in
/-- A section vanishes if it vanishes on every one-point étale scheme admitting a morphism to
`Spec L`. -/
lemma eq_zero_of_forall_map_eq_zero {V : (Spec (.of F)).Etale} (s : N.obj.obj (op V))
    (h : ∀ (Z : (Spec (.of F)).Etale) [Subsingleton Z.left] [Nonempty Z.left] (g : Z ⟶ V),
      (Z ⟶ etaleSpec F L) → N.obj.map g.op s = 0) : s = 0 := by
    let c := FieldTrace.counitMor F L V
    let τ : (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
        (FieldTrace.f F L))).obj ((FieldTrace.f F L).Etale.obj V) ⟶ etaleSpec F L :=
      MorphismProperty.Over.homMk (pullback.snd V.hom (FieldTrace.f F L)) rfl trivial
    have hc : ⋃ _ : Unit, Set.range c.left = Set.univ := by
      refine Set.eq_univ_of_forall fun v ↦ Set.mem_iUnion.2 ⟨(), ?_⟩
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := V.hom)
        (g := FieldTrace.f F L) v (Classical.arbitrary _)
        (Subsingleton.elim (α := Spec (.of F)) _ _)
      exact ⟨w, hw⟩
    refine (isSheafFor_ofArrows N (fun _ : Unit ↦ c) hc).isSeparatedFor.ext
      fun _ _ ⟨_⟩ ↦ show N.obj.map c.op s = N.obj.map c.op 0 from ?_
    rw [map_zero]
    refine ext_of_pointι N fun z ↦ ?_
    rw [map_zero, FieldTrace.map_map_apply]
    exact h _ _ (pointι _ z ≫ τ)

/-- A sheaf split by `L` with no sections over `Spec L` vanishes. -/
lemma isZero_of_isSplitBy (hN : IsSplitBy N L) (h : ∀ x : N.obj.obj (op (etaleSpec F L)), x = 0) :
    IsZero N := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  ext V s
  refine eq_zero_of_forall_map_eq_zero L s fun Z _ _ g t ↦ ?_
  obtain ⟨m, hm⟩ := (hN _ t).2 (N.obj.map g.op s)
  rw [← hm, h m, map_zero]

/-- A sheaf split by `L` whose sections over `Spec L` are killed by `n` is killed by `n`. -/
lemma nsmul_id_eq_zero_of_isSplitBy (hN : IsSplitBy N L) (n : ℕ)
    (h : ∀ x : N.obj.obj (op (etaleSpec F L)), n • x = 0) : n • 𝟙 N = 0 := by
  apply Sheaf.hom_ext
  ext V s
  change n • s = 0
  refine eq_zero_of_forall_map_eq_zero L _ fun Z _ _ g t ↦ ?_
  obtain ⟨m, hm⟩ := (hN _ t).2 (N.obj.map g.op s)
  rw [map_nsmul, ← hm, ← map_nsmul, h m, map_zero]

section FixedPoints

variable [IsGalois F L] (ℓ : ℕ) [Fact ℓ.Prime]

/-- The action of `Gal(L / F)` on the sections over `Spec L`. -/
noncomputable abbrev galAction : MulAction (L ≃ₐ[F] L) (N.obj.obj (op (etaleSpec F L))) where
  smul σ x := N.obj.map (etaleSpecMap σ.toAlgHom).op x
  one_smul x := by
    change N.obj.map (etaleSpecMap (AlgHom.id F L)).op x = x
    rw [etaleSpecMap_id, op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  mul_smul σ τ x := by
    change N.obj.map (etaleSpecMap (σ.toAlgHom.comp τ.toAlgHom)).op x = _
    rw [← etaleSpecMap_comp]
    exact (FieldTrace.map_map_apply N.obj _ _ x).symm

/-- **A nonzero global section of order `ℓ`.** If `Gal(L / F)` is an `ℓ`-group and `N` has
nonzero finite `ℓ`-primary sections over `Spec L`, then `N` has a global section of order `ℓ`:
the number of Galois invariant sections over `Spec L` is divisible by `ℓ`, so there is an
invariant section of order `ℓ`, which descends to `Spec F`. -/
lemma exists_addOrderOf_eq (hP : IsPGroup ℓ (L ≃ₐ[F] L))
    [Finite (N.obj.obj (op (etaleSpec F L)))]
    (hN : ∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0)
    (x₀ : N.obj.obj (op (etaleSpec F L))) (hx₀ : x₀ ≠ 0) :
    ∃ z : N.obj.obj (op (etalePoint F)), addOrderOf z = ℓ := by
  let := galAction (N := N) (L := L)
  let S : AddSubgroup (N.obj.obj (op (etaleSpec F L))) :=
    { carrier := MulAction.fixedPoints (L ≃ₐ[F] L) _
      add_mem' {a b} ha hb σ := by
        change N.obj.map _ (a + b) = a + b
        rw [map_add]
        exact congrArg₂ (· + ·) (ha σ) (hb σ)
      zero_mem' σ := map_zero _
      neg_mem' {a} ha σ := by
        change N.obj.map _ (-a) = -a
        rw [map_neg]
        exact congrArg _ (ha σ) }
  have := Fact.out (p := ℓ.Prime)
  -- `ℓ` divides the number of sections over `Spec L`
  have h₁ : ℓ ∣ Nat.card (N.obj.obj (op (etaleSpec F L))) := by
    obtain ⟨k, hk⟩ := hN x₀
    obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow this).1 (addOrderOf_dvd_of_nsmul_eq_zero hk)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hx₀ (AddMonoid.addOrderOf_eq_one_iff.1 (hj'.trans (pow_zero _)))
    exact (dvd_pow_self ℓ hj0).trans (hj' ▸ addOrderOf_dvd_natCard x₀)
  have h₂ : ℓ ∣ Nat.card S := by
    have := hP.card_modEq_card_fixedPoints (N.obj.obj (op (etaleSpec F L)))
    exact (Nat.modEq_zero_iff_dvd.1 (this.symm.trans (Nat.modEq_zero_iff_dvd.2 h₁)))
  obtain ⟨⟨y, hy⟩, hyℓ⟩ := exists_prime_addOrderOf_dvd_card' ℓ h₂
  obtain ⟨z, rfl⟩ := exists_map_eq_of_forall_map_etaleSpecMap_eq y fun σ ↦ hy σ
  refine ⟨z, ?_⟩
  rw [← hyℓ, AddSubgroup.addOrderOf_mk]
  exact (addOrderOf_injective (N.obj.map (etaleSpecToTerminal L).op).hom
    (injective_map_of_subsingleton N _) z).symm


/-- **Filtration of a split `ℓ`-primary sheaf by constant sheaves `ℤ/ℓ`.** Let `L / F` be a
finite Galois extension whose Galois group is an `ℓ`-group. A property of sheaves on `Spec F`
which holds for the zero sheaf, and passes from the cokernel of a monomorphism `ℤ/ℓ ⟶ N` to `N`,
holds for every sheaf split by `L` with finite `ℓ`-primary sections over `Spec L`: by induction on
the number of these sections, using a global section of order `ℓ`
(`AlgebraicGeometry.Scheme.exists_addOrderOf_eq`). -/
theorem IsSplitBy.induction (hP : IsPGroup ℓ (L ≃ₐ[F] L))
    (P : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1} → Prop)
    (h₀ : ∀ N, IsZero N → P N)
    (h₁ : ∀ (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
      (z : N.obj.obj (op (etalePoint F))) (hz : (ℓ : ℤ) • z = 0), addOrderOf z = ℓ →
        P (cokernel (constantZModHom ℓ hz)) → P N)
    (hN : IsSplitBy N L) [Finite (N.obj.obj (op (etaleSpec F L)))]
    (hNℓ : ∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0) : P N := by
  suffices H : ∀ n (N : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}),
      IsSplitBy N L → Finite (N.obj.obj (op (etaleSpec F L))) →
        (∀ x : N.obj.obj (op (etaleSpec F L)), ∃ k : ℕ, ℓ ^ k • x = 0) →
          Nat.card (N.obj.obj (op (etaleSpec F L))) = n → P N from
    H _ N hN inferInstance hNℓ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro N hN _ hNℓ hcard
  by_cases hall : ∀ x : N.obj.obj (op (etaleSpec F L)), x = 0
  · exact h₀ N (isZero_of_isSplitBy hN hall)
  push Not at hall
  obtain ⟨x₀, hx₀⟩ := hall
  obtain ⟨z, hz⟩ := exists_addOrderOf_eq ℓ hP hNℓ x₀ hx₀
  have hzℓ : (ℓ : ℤ) • z = 0 := by
    rw [natCast_zsmul, ← hz]
    exact addOrderOf_nsmul_eq_zero z
  have := mono_constantZModHom ℓ hzℓ hz
  let ι := constantZModHom ℓ hzℓ
  have hs := surjective_cokernel_π_app ι hN (etaleSpec F L) (𝟙 _)
  have : Finite ((cokernel ι).obj.obj (op (etaleSpec F L))) := Finite.of_surjective _ hs
  refine h₁ N z hzℓ hz (ih _ ?_ _ (isSplitBy_cokernel ι (isSplitBy_constantZMod ℓ) hN)
    inferInstance (fun x ↦ ?_) rfl)
  · rw [← hcard]
    refine card_cokernel_lt ι hN ((CategoryTheory.toSheafify _ ((Functor.const _).obj
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod ℓ))))).app _ (ULift.up ((1 : ℤ) : ZMod ℓ))) ?_
    change (constantZModHom ℓ hzℓ).hom.app _ _ ≠ 0
    rw [constantZModHom_app_toSheafify, zmodHom_apply, one_zsmul]
    intro h0
    have := (injective_map_of_subsingleton N (isTerminalEtalePoint.from (etaleSpec F L)))
      (h0.trans (map_zero _).symm)
    rw [this, addOrderOf_zero] at hz
    exact (Fact.out (p := ℓ.Prime)).one_lt.ne hz
  · obtain ⟨m, rfl⟩ := hs x
    obtain ⟨k, hk⟩ := hNℓ m
    exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

end FixedPoints

section Restriction

variable {F' : Type u} [Field F'] [Algebra F F'] [Algebra.Etale F F'] [Algebra F' L]
  [IsScalarTower F F' L] [Algebra.Etale F' L]

variable (F' L) in
/-- `Spec L` over `Spec F'`, viewed over `Spec F`, is `Spec L` over `Spec F`. -/
noncomputable def overMapEtaleSpecIso :
    (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale (FieldTrace.f F F'))).obj
      (etaleSpec F' L) ≅ etaleSpec F L :=
  MorphismProperty.Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq])

lemma bijective_map_overMapEtaleSpecIso_inv :
    Function.Bijective (N.obj.map (overMapEtaleSpecIso L F').inv.op) :=
  ConcreteCategory.bijective_of_isIso _

/-- **Restriction of a split sheaf.** If `N` is split by `L`, so is its restriction to an
intermediate field `F'`. -/
lemma IsSplitBy.res (hN : IsSplitBy N L) : IsSplitBy (FieldTrace.res F F' N) L := by
  intro Z _ _ t
  have : Subsingleton ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
      (FieldTrace.f F F'))).obj Z).left := ‹Subsingleton Z.left›
  have : Nonempty ((MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
      (FieldTrace.f F F'))).obj Z).left := ‹Nonempty Z.left›
  let t' := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale
    (FieldTrace.f F F'))).map t ≫ (overMapEtaleSpecIso L F').hom
  have h : ⇑((FieldTrace.res F F' N).obj.map t.op) =
      ⇑(N.obj.map t'.op) ∘ ⇑(N.obj.map (overMapEtaleSpecIso L F').inv.op) := by
    funext x
    refine Eq.trans ?_ (FieldTrace.map_map_apply N.obj _ _ x).symm
    simp [t']
    rfl
  exact h ▸ (hN _ t').comp bijective_map_overMapEtaleSpecIso_inv

end Restriction

end Split

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {F : Type u} [Field F]

instance (V : (Spec (.of F)).Etale) (v : V.left) : IsOpenImmersion (pointι V v).left :=
  inferInstanceAs (IsOpenImmersion (pointOpens V v).ι)

/-- A morphism from a one-point scheme factors through the open point of its image. -/
lemma exists_comp_pointι_eq {Z V : (Spec (.of F)).Etale} (g : Z ⟶ V) (v : V.left)
    (hv : ∀ z, g.left z = v) : ∃ g' : Z ⟶ pointObj V v, g' ≫ pointι V v = g := by
  have hr : Set.range g.left ⊆ Set.range (pointι V v).left := by
    rintro _ ⟨z, rfl⟩
    rw [hv z]
    exact ⟨⟨_, rfl⟩, rfl⟩
  refine ⟨MorphismProperty.Over.homMk (IsOpenImmersion.lift (pointι V v).left g.left hr)
    (by
      rw [← MorphismProperty.Over.w (pointι V v), ← Category.assoc,
        IsOpenImmersion.lift_fac]
      exact MorphismProperty.Over.w g) _root_.trivial, ?_⟩
  exact MorphismProperty.Over.Hom.ext (IsOpenImmersion.lift_fac _ _ _)

/-- Two morphisms into a one-point scheme, from one-point schemes, are dominated by a common
one-point scheme. -/
lemma exists_comp_eq_comp {Y Z W : (Spec (.of F)).Etale} [Subsingleton Y.left]
    [Nonempty Z.left] [Nonempty W.left] (h : Z ⟶ Y) (w : W ⟶ Y) :
    ∃ (P : (Spec (.of F)).Etale) (_ : Subsingleton P.left) (_ : Nonempty P.left) (p₁ : P ⟶ Z)
      (p₂ : P ⟶ W), p₁ ≫ h = p₂ ≫ w := by
  have : AlgebraicGeometry.Etale w.left := by
    have := W.prop
    have := Y.prop
    have : AlgebraicGeometry.Etale (w.left ≫ Y.hom) := by
      rw [MorphismProperty.Over.w w]; exact W.prop
    exact AlgebraicGeometry.Etale.of_comp w.left Y.hom
  let T : (Spec (.of F)).Etale := MorphismProperty.Over.mk ⊤
    (pullback.fst h.left w.left ≫ Z.hom) (by have := Z.prop; infer_instance)
  let q₁ : T ⟶ Z := MorphismProperty.Over.homMk (pullback.fst h.left w.left) rfl _root_.trivial
  let q₂ : T ⟶ W := MorphismProperty.Over.homMk (pullback.snd h.left w.left) (by
    change _ ≫ W.hom = _ ≫ Z.hom
    rw [← MorphismProperty.Over.w w, ← Category.assoc, ← pullback.condition, Category.assoc,
      MorphismProperty.Over.w h]) _root_.trivial
  obtain ⟨t, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h.left) (g := w.left)
    (Classical.arbitrary Z.left) (Classical.arbitrary W.left) (Subsingleton.elim _ _)
  refine ⟨pointObj T t, inferInstance, inferInstance, pointι T t ≫ q₁, pointι T t ≫ q₂, ?_⟩
  rw [Category.assoc, Category.assoc]
  congr 1
  exact MorphismProperty.Over.Hom.ext pullback.condition

section SplitSubsheaf

variable (M : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
  (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]
  (A : AddSubgroup (M.obj.obj (op (etaleSpec F L))))

/-- The sections of `M` over `V` which, on every one-point étale scheme `Z` over `V` admitting a
morphism `t : Z ⟶ Spec L`, are restrictions along `t` of elements of `A`. -/
def splitSubgroup (V : (Spec (.of F)).Etale) : AddSubgroup (M.obj.obj (op V)) where
  carrier := {s | ∀ (Z : (Spec (.of F)).Etale) [Subsingleton Z.left] [Nonempty Z.left]
    (g : Z ⟶ V) (t : Z ⟶ etaleSpec F L), M.obj.map g.op s ∈ A.map (M.obj.map t.op).hom}
  add_mem' {a b} ha hb Z _ _ g t := by
    rw [map_add]
    exact add_mem (ha Z g t) (hb Z g t)
  zero_mem' Z _ _ g t := by
    rw [map_zero]
    exact zero_mem _
  neg_mem' {a} ha Z _ _ g t := by
    rw [map_neg]
    exact neg_mem (ha Z g t)

variable {M L A}

lemma map_mem_splitSubgroup {V V' : (Spec (.of F)).Etale} (h : V' ⟶ V) {s : M.obj.obj (op V)}
    (hs : s ∈ splitSubgroup M L A V) : M.obj.map h.op s ∈ splitSubgroup M L A V' :=
  fun Z _ _ g t ↦ by
    rw [FieldTrace.map_map_apply]
    exact hs Z (g ≫ h) t

lemma mem_splitSubgroup_of_comp {Y W : (Spec (.of F)).Etale} [Subsingleton Y.left]
    [Nonempty W.left] (w : W ⟶ Y) {x : M.obj.obj (op Y)}
    (hx : M.obj.map w.op x ∈ splitSubgroup M L A W) : x ∈ splitSubgroup M L A Y := by
  intro Z _ _ h t
  obtain ⟨P, _, _, p₁, p₂, hp⟩ := exists_comp_eq_comp h w
  obtain ⟨a, ha, hax⟩ := AddSubgroup.mem_map.1 (hx P p₂ (p₁ ≫ t))
  refine AddSubgroup.mem_map.2 ⟨a, ha, injective_map_of_subsingleton M p₁
    ((FieldTrace.map_map_apply M.obj _ _ a).trans (hax.trans ?_))⟩
  rw [FieldTrace.map_map_apply M.obj p₂ w x, ← hp, ← FieldTrace.map_map_apply]

lemma mem_splitSubgroup_of_pointι {V : (Spec (.of F)).Etale} {s : M.obj.obj (op V)}
    (hs : ∀ v, M.obj.map (pointι V v).op s ∈ splitSubgroup M L A (pointObj V v)) :
    s ∈ splitSubgroup M L A V := by
  intro Z _ _ g t
  let z : Z.left := Classical.arbitrary _
  obtain ⟨g', hg'⟩ := exists_comp_pointι_eq g (g.left z) fun z' ↦ by rw [Subsingleton.elim z' z]
  rw [← hg', ← FieldTrace.map_map_apply]
  exact hs _ Z g' t

lemma mem_splitSubgroup_of_mem_sieve {V : (Spec (.of F)).Etale} {S : Sieve V}
    (hS : S ∈ (Spec (.of F)).smallEtaleTopology V) {s : M.obj.obj (op V)}
    (h : ∀ (W : (Spec (.of F)).Etale) (g : W ⟶ V), S g → M.obj.map g.op s ∈ splitSubgroup M L A W) :
    s ∈ splitSubgroup M L A V := by
  refine mem_splitSubgroup_of_pointι fun v ↦ ?_
  obtain ⟨W, g, w, hg, hw⟩ := exists_of_mem_smallEtaleTopology hS v
  obtain ⟨g', hg'⟩ := exists_comp_pointι_eq (pointι W w ≫ g) v fun z ↦ by
    rw [← hw]
    change g.left ((pointι W w).left z) = _
    congr 1
    obtain ⟨z, hz⟩ := z
    exact Set.mem_singleton_iff.1 (show z ∈ ({w} : Set W.left) from hz)
  refine mem_splitSubgroup_of_comp g' ?_
  rw [FieldTrace.map_map_apply, hg', ← FieldTrace.map_map_apply]
  exact map_mem_splitSubgroup _ (h W g hg)

section SubgroupPresheaf

variable (M) (P : ∀ V : (Spec (.of F)).Etale, AddSubgroup (M.obj.obj (op V)))
  (hP : ∀ {V V' : (Spec (.of F)).Etale} (h : V' ⟶ V) {s : M.obj.obj (op V)}, s ∈ P V →
    M.obj.map h.op s ∈ P V')

/-- The subpresheaf of `M` given by a restriction-stable family of subgroups. -/
noncomputable def subgroupPresheaf : (Spec (.of F)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj V := AddCommGrpCat.of (P V.unop)
  map {V V'} h := AddCommGrpCat.ofHom (AddMonoidHom.codRestrict
    ((M.obj.map h).hom.comp (P V.unop).subtype) _ fun x ↦ hP h.unop x.2)
  map_id V := by
    ext x
    simp [AddMonoidHom.codRestrict]
  map_comp f g := by
    ext x
    simp [AddMonoidHom.codRestrict]

/-- A restriction-stable family of subgroups of the sections of a sheaf which is local for the
covering sieves is a sheaf. -/
lemma isSheaf_subgroupPresheaf
    (hloc : ∀ {V : (Spec (.of F)).Etale} {S : Sieve V}, S ∈ (Spec (.of F)).smallEtaleTopology V →
      ∀ s : M.obj.obj (op V), (∀ (W : (Spec (.of F)).Etale) (g : W ⟶ V), S g →
        M.obj.map g.op s ∈ P W) → s ∈ P V) :
    Presheaf.IsSheaf (Spec (.of F)).smallEtaleTopology (subgroupPresheaf M P hP) := by
  rw [Presheaf.isSheaf_iff_isSheaf_forget (s := CategoryTheory.forget AddCommGrpCat),
    isSheaf_iff_isSheaf_of_type]
  intro V S hS
  have hM : Presieve.IsSheafFor (M.obj ⋙ CategoryTheory.forget _) S.arrows :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ M.obj (CategoryTheory.forget AddCommGrpCat) M.property)
    S hS
  intro x hx
  let x' : Presieve.FamilyOfElements (M.obj ⋙ CategoryTheory.forget _) S.arrows :=
    fun W g hg ↦ (x g hg).1
  have hx' : x'.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w ↦
    congrArg Subtype.val (hx g₁ g₂ h₁ h₂ w)
  obtain ⟨s, hs, huniq⟩ := hM x' hx'
  have hmem : s ∈ P V := hloc hS s fun W g hg ↦ by
    rw [show M.obj.map g.op s = (x g hg).1 from hs g hg]
    exact (x g hg).2
  exact ⟨⟨s, hmem⟩, fun W g hg ↦ Subtype.ext (hs g hg),
    fun t ht ↦ Subtype.ext (huniq t.1 fun W g hg ↦ congrArg Subtype.val (ht g hg))⟩

end SubgroupPresheaf

variable (M L A) in
/-- The subpresheaf of `M` of sections split by `L` with values in `A`. -/
noncomputable abbrev splitPresheaf : (Spec (.of F)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  subgroupPresheaf M (splitSubgroup M L A) fun h _ hs ↦ map_mem_splitSubgroup h hs

lemma isSheaf_splitPresheaf :
    Presheaf.IsSheaf (Spec (.of F)).smallEtaleTopology (splitPresheaf M L A) :=
  isSheaf_subgroupPresheaf _ _ _ fun hS _ h ↦ mem_splitSubgroup_of_mem_sieve hS h

variable (M L A) in
/-- The subsheaf of `M` of sections split by `L` with values in `A`. -/
noncomputable def splitSheaf : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨splitPresheaf M L A, isSheaf_splitPresheaf⟩

variable (M L A) in
/-- The inclusion of `splitSheaf M L A` into `M`. -/
noncomputable def splitSheafι : splitSheaf M L A ⟶ M :=
  ⟨{ app V := AddCommGrpCat.ofHom (splitSubgroup M L A V.unop).subtype
     naturality _ _ _ := rfl }⟩

instance : Mono (splitSheafι M L A) := by
  have (V : (Spec (.of F)).Etaleᵒᵖ) : Mono ((splitSheafι M L A).hom.app V) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono (splitSheafι M L A).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

lemma mem_of_mem_splitSubgroup_etaleSpec {s : M.obj.obj (op (etaleSpec F L))}
    (hs : s ∈ splitSubgroup M L A (etaleSpec F L)) : s ∈ A := by
  obtain ⟨a, ha, has⟩ := AddSubgroup.mem_map.1 (hs _ (𝟙 _) (𝟙 _))
  rw [op_id, CategoryTheory.Functor.map_id] at has
  exact (show a = s from has) ▸ ha

lemma mem_splitSubgroup_etaleSpec [IsGalois F L]
    (hA : ∀ σ : L ≃ₐ[F] L, ∀ a ∈ A, M.obj.map (etaleSpecMap σ.toAlgHom).op a ∈ A) {a}
    (ha : a ∈ A) : a ∈ splitSubgroup M L A (etaleSpec F L) := by
  intro Z _ _ g t
  obtain ⟨σ, hσ⟩ := exists_eq_comp_etaleSpecMap L t g
  rw [hσ, ← FieldTrace.map_map_apply]
  exact ⟨_, hA σ a ha, rfl⟩

lemma isSplitBy_splitSheaf [IsGalois F L]
    (hA : ∀ σ : L ≃ₐ[F] L, ∀ a ∈ A, M.obj.map (etaleSpecMap σ.toAlgHom).op a ∈ A) :
    IsSplitBy (splitSheaf M L A) L := by
  intro Z _ _ t
  refine ⟨fun x y h ↦ Subtype.ext (injective_map_of_subsingleton M t
    (congrArg Subtype.val h)), fun y ↦ ?_⟩
  obtain ⟨a, ha, hay⟩ := AddSubgroup.mem_map.1 (y.2 Z (𝟙 _) t)
  rw [op_id, CategoryTheory.Functor.map_id] at hay
  exact ⟨⟨a, mem_splitSubgroup_etaleSpec hA ha⟩, Subtype.ext hay⟩

instance [Finite A] : Finite ((splitSheaf M L A).obj.obj (op (etaleSpec F L))) :=
  Finite.of_injective (β := A) (fun x ↦ ⟨x.1, mem_of_mem_splitSubgroup_etaleSpec x.2⟩)
    (by intro x y h; simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)

end SplitSubsheaf

end AlgebraicGeometry.Scheme

/-- **Common Galois extension.** Two finite separable extensions of a field embed into a common
finite Galois extension. -/
lemma exists_isGalois_algHom_algHom (F : Type u) [Field F] (E₁ E₂ : Type u) [Field E₁] [Field E₂]
    [Algebra F E₁] [Algebra F E₂] [Algebra.Etale F E₁] [Algebra.Etale F E₂] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra.Etale F L) (_ : IsGalois F L),
      Nonempty (E₁ →ₐ[F] L) ∧ Nonempty (E₂ →ₐ[F] L) := by
  have : Module.Finite F E₁ := Algebra.FormallyUnramified.finite_of_free F E₁
  have : Module.Finite F E₂ := Algebra.FormallyUnramified.finite_of_free F E₂
  have : Algebra.IsSeparable F E₁ := Algebra.FormallyUnramified.isSeparable F E₁
  have : Algebra.IsSeparable F E₂ := Algebra.FormallyUnramified.isSeparable F E₂
  let Ω := SeparableClosure E₁
  have : Algebra.IsSeparable F Ω := Algebra.IsSeparable.trans F E₁ Ω
  have : IsSepClosure F Ω := ⟨inferInstance, inferInstance⟩
  let ι₁ : E₁ →ₐ[F] Ω := IsScalarTower.toAlgHom F E₁ Ω
  let ι₂ : E₂ →ₐ[F] Ω := IsSepClosed.lift
  let E : IntermediateField F Ω := ι₁.fieldRange ⊔ ι₂.fieldRange
  have : FiniteDimensional F ι₁.fieldRange :=
    (AlgEquiv.ofInjectiveField ι₁).toLinearEquiv.finiteDimensional
  have : FiniteDimensional F ι₂.fieldRange :=
    (AlgEquiv.ofInjectiveField ι₂).toLinearEquiv.finiteDimensional
  have : FiniteDimensional F E := IntermediateField.finiteDimensional_sup _ _
  let L := IntermediateField.normalClosure F E Ω
  have hE : E ≤ L := IntermediateField.le_normalClosure E
  have : Algebra.IsSeparable F L := Algebra.isSeparable_tower_bot_of_isSeparable F L Ω
  have : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable F L
  have : Algebra.Etale F L :=
    ⟨inferInstance, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨ι₁.codRestrict L.toSubalgebra fun x ↦ hE (le_sup_left (a := ι₁.fieldRange) ⟨x, rfl⟩)⟩,
    ⟨ι₂.codRestrict L.toSubalgebra fun x ↦ hE (le_sup_right (b := ι₂.fieldRange) ⟨x, rfl⟩)⟩⟩

lemma AddSubgroup.finite_closure_of_isOfFinAddOrder {G : Type*} [AddCommGroup G] {s : Set G}
    (hs : s.Finite) (ht : ∀ x ∈ s, IsOfFinAddOrder x) : Finite (AddSubgroup.closure s) := by
  have := hs.to_subtype
  have : AddGroup.FG (AddSubgroup.closure s) := AddGroup.closure_finite_fg s
  have : Module.Finite ℤ (AddSubgroup.closure s) := Module.Finite.iff_addGroup_fg.2 this
  refine Module.finite_of_fg_torsion _ fun x ↦ ?_
  have hx : (x : G) ∈ AddCommGroup.torsion G :=
    (AddSubgroup.closure_le _).2 (fun y hy ↦ ht y hy) x.2
  have hx' : IsOfFinAddOrder x := AddSubmonoid.isOfFinAddOrder_coe.1 hx
  refine ⟨⟨addOrderOf x, mem_nonZeroDivisors_of_ne_zero
    (by exact_mod_cast hx'.addOrderOf_pos.ne')⟩, ?_⟩
  change ((addOrderOf x : ℕ) : ℤ) • x = 0
  rw [natCast_zsmul, addOrderOf_nsmul_eq_zero]

namespace AlgebraicGeometry.Scheme

variable {F : Type u} [Field F] (M : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1})
  (L : Type u) [Field L] [Algebra F L] [Algebra.Etale F L]

section Orbit

/-- The subgroup generated by the Galois orbits of a set of sections over `Spec L`. -/
noncomputable def orbitClosure (B : Set (M.obj.obj (op (etaleSpec F L)))) :
    AddSubgroup (M.obj.obj (op (etaleSpec F L))) :=
  AddSubgroup.closure {y | ∃ (σ : L ≃ₐ[F] L) (b : M.obj.obj (op (etaleSpec F L))), b ∈ B ∧
    M.obj.map (etaleSpecMap σ.toAlgHom).op b = y}

variable {M L}

lemma subset_orbitClosure (B : Set (M.obj.obj (op (etaleSpec F L)))) :
    B ⊆ orbitClosure M L B := fun b hb ↦ AddSubgroup.subset_closure ⟨1, b, hb, by
  change M.obj.map (etaleSpecMap (AlgHom.id F L)).op b = b
  rw [GaloisCech.etaleSpecMap_id, op_id, CategoryTheory.Functor.map_id,
    ConcreteCategory.id_apply]⟩

lemma map_mem_orbitClosure (B : Set (M.obj.obj (op (etaleSpec F L)))) (σ : L ≃ₐ[F] L)
    {a : M.obj.obj (op (etaleSpec F L))} (ha : a ∈ orbitClosure M L B) :
    M.obj.map (etaleSpecMap σ.toAlgHom).op a ∈ orbitClosure M L B := by
  have : orbitClosure M L B ≤ (orbitClosure M L B).comap (M.obj.map
      (etaleSpecMap σ.toAlgHom).op).hom := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨τ, b, hb, rfl⟩
    have hcomp : (σ * τ).toAlgHom = σ.toAlgHom.comp τ.toAlgHom := AlgHom.ext fun _ ↦ rfl
    have heq : M.obj.map (etaleSpecMap (σ * τ).toAlgHom).op b =
        M.obj.map (etaleSpecMap σ.toAlgHom).op (M.obj.map (etaleSpecMap τ.toAlgHom).op b) := by
      rw [FieldTrace.map_map_apply, etaleSpecMap_comp, hcomp]
    exact AddSubgroup.mem_comap.2 (AddSubgroup.subset_closure ⟨σ * τ, b, hb, heq⟩)
  exact AddSubgroup.mem_comap.1 (this ha)

lemma finite_orbitClosure (B : Set (M.obj.obj (op (etaleSpec F L)))) (hB : B.Finite)
    (ht : ∀ b ∈ B, IsOfFinAddOrder b) [Finite (L ≃ₐ[F] L)] :
    Finite (orbitClosure M L B) := by
  refine AddSubgroup.finite_closure_of_isOfFinAddOrder ?_ ?_
  · have : {y | ∃ (σ : L ≃ₐ[F] L) (b : M.obj.obj (op (etaleSpec F L))), b ∈ B ∧
        M.obj.map (etaleSpecMap σ.toAlgHom).op b = y} =
        ⋃ σ : L ≃ₐ[F] L, (M.obj.map (etaleSpecMap σ.toAlgHom).op) '' B := by
      ext y
      simp
    rw [this]
    exact Set.finite_iUnion fun σ ↦ hB.image _
  · rintro _ ⟨σ, b, hb, rfl⟩
    exact AddMonoidHom.isOfFinAddOrder (M.obj.map (etaleSpecMap σ.toAlgHom).op).hom (ht b hb)

end Orbit

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

variable {F : Type u} [Field F] {M : Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1}}

lemma splitSubgroup_mono {L L' : Type u} [Field L] [Algebra F L] [Algebra.Etale F L] [Field L']
    [Algebra F L'] [Algebra.Etale F L'] (ι : L →ₐ[F] L') {A : AddSubgroup (M.obj.obj
      (op (etaleSpec F L)))} {A' : AddSubgroup (M.obj.obj (op (etaleSpec F L')))}
    (h : ∀ a ∈ A, M.obj.map (etaleSpecMap ι).op a ∈ A') (V : (Spec (.of F)).Etale) :
    splitSubgroup M L A V ≤ splitSubgroup M L' A' V := by
  intro s hs Z _ _ g t
  obtain ⟨a, ha, has⟩ := AddSubgroup.mem_map.1 (hs Z g (t ≫ etaleSpecMap ι))
  refine AddSubgroup.mem_map.2 ⟨_, h a ha, ?_⟩
  rw [FieldTrace.map_map_apply]
  exact has

/-- A section of order `n` over a one-point scheme has finite order if the sheaf is torsion. -/
lemma isOfFinAddOrder_of_isTorsion (hM : M.IsTorsion) {Y : (Spec (.of F)).Etale}
    [Subsingleton Y.left] [Nonempty Y.left] (x : M.obj.obj (op Y)) : IsOfFinAddOrder x := by
  obtain ⟨S, hS, hSx⟩ := hM (U := op Y) x
  obtain ⟨W, g, w, hg, -⟩ := exists_of_mem_smallEtaleTopology hS (Classical.arbitrary Y.left)
  have : Nonempty W.left := ⟨w⟩
  rw [← addOrderOf_pos_iff, ← addOrderOf_injective (M.obj.map g.op).hom
    (injective_map_of_subsingleton M g) x, addOrderOf_pos_iff]
  exact hSx hg

/-- Every section of a torsion sheaf over a one-point étale scheme is split by some finite Galois
extension, with values in the subgroup generated by a finite Galois orbit. -/
lemma exists_mem_splitSubgroup (hM : M.IsTorsion) {Y : (Spec (.of F)).Etale}
    [Subsingleton Y.left] [Nonempty Y.left] (x : M.obj.obj (op Y)) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra.Etale F L) (_ : IsGalois F L)
      (B : Set (M.obj.obj (op (etaleSpec F L)))), B.Finite ∧ (∀ b ∈ B, IsOfFinAddOrder b) ∧
        x ∈ splitSubgroup M L (orbitClosure M L B) Y := by
  obtain ⟨E, _, _, _, g₀, -, -⟩ := exists_etaleSpec_field_left_apply_eq Y (Classical.arbitrary _)
  obtain ⟨L, _, _, _, _, ⟨ι⟩, -⟩ := exists_isGalois_algHom_algHom F E E
  let w := etaleSpecMap ι ≫ g₀
  refine ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, {M.obj.map w.op x},
    Set.finite_singleton _, fun b hb ↦ hb ▸ isOfFinAddOrder_of_isTorsion hM _,
    mem_splitSubgroup_of_comp w (mem_splitSubgroup_etaleSpec
      (fun σ a ha ↦ map_mem_orbitClosure _ σ ha) (subset_orbitClosure _ rfl))⟩

section Family

variable (M)

/-- The families of subgroups `V ↦ splitSubgroup M L A V`, for `L / F` finite Galois and `A`
generated by the Galois orbits of finitely many sections of finite order over `Spec L`. -/
def SplitFamily : Type (u + 1) :=
  {P : ∀ V : (Spec (.of F)).Etale, AddSubgroup (M.obj.obj (op V)) //
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra.Etale F L) (_ : IsGalois F L)
      (B : Set (M.obj.obj (op (etaleSpec F L)))), B.Finite ∧ (∀ b ∈ B, IsOfFinAddOrder b) ∧
        P = splitSubgroup M L (orbitClosure M L B)}

instance : PartialOrder (SplitFamily M) := Subtype.partialOrder _

instance : Nonempty (SplitFamily M) :=
  ⟨⟨_, F, inferInstance, inferInstance, inferInstance, inferInstance, ∅, Set.finite_empty,
    by simp, rfl⟩⟩

instance : IsDirected (SplitFamily M) (· ≤ ·) where
  directed := by
    rintro ⟨_, L₁, _, _, _, _, B₁, hB₁, ht₁, rfl⟩ ⟨_, L₂, _, _, _, _, B₂, hB₂, ht₂, rfl⟩
    obtain ⟨L, _, _, _, _, ⟨ι₁⟩, ⟨ι₂⟩⟩ := exists_isGalois_algHom_algHom F L₁ L₂
    have : FiniteDimensional F L₁ := Algebra.FormallyUnramified.finite_of_free F L₁
    have : FiniteDimensional F L₂ := Algebra.FormallyUnramified.finite_of_free F L₂
    have := finite_orbitClosure (M := M) _ hB₁ ht₁
    have := finite_orbitClosure (M := M) _ hB₂ ht₂
    let B : Set (M.obj.obj (op (etaleSpec F L))) :=
      (M.obj.map (etaleSpecMap ι₁).op) '' (orbitClosure M L₁ B₁ : Set _) ∪
        (M.obj.map (etaleSpecMap ι₂).op) '' (orbitClosure M L₂ B₂ : Set _)
    have hB : B.Finite := (Set.toFinite _).image _ |>.union ((Set.toFinite _).image _)
    have ht : ∀ b ∈ B, IsOfFinAddOrder b := by
      rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
      · exact AddMonoidHom.isOfFinAddOrder _
          (AddSubmonoid.isOfFinAddOrder_coe.2 (isOfFinAddOrder_of_finite (⟨a, ha⟩ :
            orbitClosure M L₁ B₁)))
      · exact AddMonoidHom.isOfFinAddOrder _
          (AddSubmonoid.isOfFinAddOrder_coe.2 (isOfFinAddOrder_of_finite (⟨a, ha⟩ :
            orbitClosure M L₂ B₂)))
    refine ⟨⟨_, L, inferInstance, inferInstance, inferInstance, inferInstance, B, hB, ht, rfl⟩,
      fun V ↦ splitSubgroup_mono ι₁ (fun a ha ↦ subset_orbitClosure _ (Or.inl ⟨a, ha, rfl⟩)) V,
      fun V ↦ splitSubgroup_mono ι₂ (fun a ha ↦ subset_orbitClosure _ (Or.inr ⟨a, ha, rfl⟩)) V⟩


variable {M} in
lemma SplitFamily.map_mem (j : SplitFamily M) {V V' : (Spec (.of F)).Etale} (h : V' ⟶ V)
    {s : M.obj.obj (op V)} : s ∈ j.1 V → M.obj.map h.op s ∈ j.1 V' := by
  obtain ⟨_, L, _, _, _, _, B, -, -, rfl⟩ := j
  exact fun hs ↦ map_mem_splitSubgroup h hs

variable {M} in
lemma SplitFamily.isSheaf (j : SplitFamily M) :
    Presheaf.IsSheaf (Spec (.of F)).smallEtaleTopology
      (subgroupPresheaf M j.1 (SplitFamily.map_mem j)) := by
  obtain ⟨_, L, _, _, _, _, B, -, -, rfl⟩ := j
  exact isSheaf_splitPresheaf

variable {M} in
/-- The sheaf of sections in a split family. -/
noncomputable def SplitFamily.sheaf (j : SplitFamily M) :
    Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1} :=
  ⟨_, SplitFamily.isSheaf j⟩

/-- The diagram of the subsheaves of a split family. -/
noncomputable def SplitFamily.diagram :
    SplitFamily M ⥤ Sheaf (Spec (.of F)).smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj j := j.sheaf
  map h := ⟨NatTrans.mk (fun V ↦ AddCommGrpCat.ofHom (AddSubgroup.inclusion (leOfHom h V.unop)))
    (fun _ _ _ ↦ rfl)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The cocone of the subsheaves of a split family, with point `M`. -/
noncomputable def SplitFamily.cocone : Cocone (SplitFamily.diagram M) where
  pt := M
  ι := NatTrans.mk (fun j ↦ ⟨NatTrans.mk (fun V ↦ AddCommGrpCat.ofHom (j.1 V.unop).subtype)
    (fun _ _ _ ↦ rfl)⟩) (fun _ _ _ ↦ rfl)

instance SplitFamily.mono_cocone_ι (j : SplitFamily M) : Mono ((SplitFamily.cocone M).ι.app j) := by
  have (V : (Spec (.of F)).Etaleᵒᵖ) : Mono (((SplitFamily.cocone M).ι.app j).hom.app V) :=
    (AddCommGrpCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono ((SplitFamily.cocone M).ι.app j).hom := NatTrans.mono_of_mono_app _
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _

variable {M} in
/-- Each subsheaf of the split family is split by a finite Galois extension, with finite sections
over it. -/
lemma SplitFamily.exists_isSplitBy (j : SplitFamily M) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra F L) (_ : Algebra.Etale F L) (_ : IsGalois F L),
      IsSplitBy ((SplitFamily.diagram M).obj j) L ∧
        Finite (((SplitFamily.diagram M).obj j).obj.obj (op (etaleSpec F L))) := by
  obtain ⟨_, L, _, _, _, _, B, hB, ht, rfl⟩ := j
  have : FiniteDimensional F L := Algebra.FormallyUnramified.finite_of_free F L
  have := finite_orbitClosure (M := M) _ hB ht
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    isSplitBy_splitSheaf (fun σ a ha ↦ map_mem_orbitClosure _ σ ha),
    inferInstanceAs (Finite ((splitSheaf M L (orbitClosure M L B)).obj.obj
      (op (etaleSpec F L))))⟩

end Family

end AlgebraicGeometry.Scheme
