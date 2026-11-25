/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.LocalRing.Module
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!
# Perfect complexes with prescribed amplitude

Let `R` be a Noetherian commutative ring. An object `C` of `D(R)` with finitely generated
cohomology modules and Tor amplitude in `[a, b]` is represented by a complex of finitely
generated projective `R`-modules concentrated in degrees `[a, b]` (Stacks, Tag 0658). Over a
local ring the terms can be taken finite free.

This sharpens `DerivedCategory.isPerfect_of_finiteTorAmplitude`, which only produces some
bounded complex of finitely generated projective modules: the induction on the length of the
Tor amplitude is the same, but keeps track of the degrees.

## Main statements

- `DerivedCategory.exists_iso_Q_obj_projective_of_torAmplitudeIn`
  (`lemma-perfect-complexes-geometric-point`): the model by finite projective modules in degrees
  `[a, b]`.
- `DerivedCategory.exists_iso_Q_obj_free_of_torAmplitudeIn`
  (`lemma-perfect-complexes-geometric-point`): over a local ring, the model by finite free modules
  in degrees `[a, b]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- `C` is represented by a complex of finitely generated projective `R`-modules concentrated in
degrees `[a, b]`. -/
private def HasProjectiveModelIn (a b : ℤ) (C : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P)

private lemma HasProjectiveModelIn.of_iso {a b : ℤ} {C D : DerivedCategory (ModuleCat.{u} R)}
    (hC : HasProjectiveModelIn a b C) (e : C ≅ D) : HasProjectiveModelIn a b D := by
  obtain ⟨P, ha, hb, hP, ⟨e'⟩⟩ := hC
  exact ⟨P, ha, hb, hP, ⟨e.symm ≪≫ e'⟩⟩

private lemma HasProjectiveModelIn.mono {a b a' b' : ℤ} (ha : a' ≤ a) (hb : b ≤ b')
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : HasProjectiveModelIn a b C) :
    HasProjectiveModelIn a' b' C := by
  obtain ⟨P, _, _, hP, e⟩ := hC
  exact ⟨P, CochainComplex.isStrictlyGE_of_ge P a' a ha,
    CochainComplex.isStrictlyLE_of_le P b b' hb, hP, e⟩

private lemma HasProjectiveModelIn.shift {a b : ℤ} {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : HasProjectiveModelIn a b C) (n : ℤ) : HasProjectiveModelIn (a - n) (b - n) (C⟦n⟧) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := hC
  exact ⟨P⟦n⟧, P.isStrictlyGE_shift a n (a - n) (by omega),
    P.isStrictlyLE_shift b n (b - n) (by omega), fun i ↦ hP (i + n),
    ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩⟩

/-- The mapping cone of a morphism between complexes of finitely generated projective modules in
degrees `[a₁, b₁]` and `[a₂, b₂]` is such a complex in degrees `[min (a₁ - 1) a₂, max (b₁ - 1) b₂]`.
-/
private lemma hasProjectiveModelIn_Q_obj_mappingCone {P₁ P₂ : CochainComplex (ModuleCat.{u} R) ℤ}
    (φ : P₁ ⟶ P₂) (a₁ b₁ a₂ b₂ : ℤ) [P₁.IsStrictlyGE a₁] [P₁.IsStrictlyLE b₁]
    [P₂.IsStrictlyGE a₂] [P₂.IsStrictlyLE b₂]
    (h₁ : ∀ i, Module.Projective R (P₁.X i) ∧ Module.Finite R (P₁.X i))
    (h₂ : ∀ i, Module.Projective R (P₂.X i) ∧ Module.Finite R (P₂.X i)) :
    HasProjectiveModelIn (min (a₁ - 1) a₂) (max (b₁ - 1) b₂)
      (Q.obj (CochainComplex.mappingCone φ)) := by
  refine ⟨CochainComplex.mappingCone φ, CochainComplex.isStrictlyGE_mappingCone φ a₁ a₂ _, ?_,
    fun i ↦ ?_, ⟨Iso.refl _⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega), P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  · let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
      ModuleCat.biprodIsoProd (P₁.X (i + 1)) (P₂.X i)
    have := (h₁ (i + 1)).1
    have := (h₁ (i + 1)).2
    have := (h₂ i).1
    have := (h₂ i).2
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- Extensions: in a distinguished triangle `C₁ ⟶ C₂ ⟶ C₃ ⟶ C₁[1]` with `C₁` and `C₃`
represented by complexes of finitely generated projective modules in degrees `[a₁, b₁]` and
`[a₃, b₃]`, the object `C₂` is represented by such a complex in degrees
`[min a₁ a₃, max b₁ b₃]`. -/
private lemma hasProjectiveModelIn_obj₂_of_distTriang
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) {a₁ b₁ a₃ b₃ : ℤ} (h₁ : HasProjectiveModelIn a₁ b₁ T.obj₁)
    (h₃ : HasProjectiveModelIn a₃ b₃ T.obj₃) :
    HasProjectiveModelIn (min a₁ a₃) (max b₁ b₃) T.obj₂ := by
  obtain ⟨P₁, _, _, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, _, _, hP₃, ⟨e₃⟩⟩ := h₃
  have : ∀ n, Projective (P₃.X n) := fun n ↦ by
    have := (hP₃ n).1
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : P₃.IsKProjective := CochainComplex.isKProjective_of_projective _ b₃
  have := P₁.isStrictlyGE_shift a₁ 1 (a₁ - 1) (by omega)
  have := P₁.isStrictlyLE_shift b₁ 1 (b₁ - 1) (by omega)
  obtain ⟨ψ, hψ⟩ := CochainComplex.IsKProjective.exists_Q_map_eq P₃ (P₁⟦(1 : ℤ)⟧)
    (e₃.inv ≫ T.mor₃ ≫ e₁.hom⟦(1 : ℤ)⟧' ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).inv)
  have hcomm : Q.map ψ ≫ ((Q.commShiftIso (1 : ℤ)).app P₁).hom ≫ e₁.inv⟦(1 : ℤ)⟧' =
      e₃.inv ≫ T.mor₃ := by
    rw [hψ]
    simp [← Functor.map_comp]
  obtain ⟨f, -⟩ := Pretriangulated.exists_iso_of_arrow_iso _ _
    (mappingCone_triangle_distinguished ψ)
    (Pretriangulated.rot_of_distTriang _ (Pretriangulated.rot_of_distTriang _ hT))
    (Arrow.isoMk e₃.symm (((Q.commShiftIso (1 : ℤ)).app P₁) ≪≫ (shiftFunctor _ 1).mapIso e₁.symm)
      hcomm.symm)
  have hcone := hasProjectiveModelIn_Q_obj_mappingCone ψ a₃ b₃ (a₁ - 1) (b₁ - 1) hP₃
    fun i ↦ hP₁ (i + 1)
  refine (((hcone.of_iso (Pretriangulated.Triangle.π₃.mapIso f)).shift (-1)).of_iso
    ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)).mono ?_ ?_ <;> omega

section FiniteTorAmplitude

variable [IsNoetherianRing R]

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
/-- A complex of flat modules concentrated in degree `b`, whose cohomology in degree `b` is
finitely generated, is a complex of finitely generated projective modules: its term in degree
`b` is its cohomology, a finitely presented flat module. -/
private lemma projective_finite_of_flat (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyGE b] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hb : Module.Finite R (P.homology b)) (i : ℤ) :
    Module.Projective R (P.X i) ∧ Module.Finite R (P.X i) := by
  have : Module.Flat R (P.X i) := (ModuleCat.flat_iff_flat _).1 (hP i)
  have : Module.Finite R (P.X i) := by
    by_cases hi : i = b
    · subst hi
      have := P.isIso_homologyπ (i - 1) i (by simp)
        ((P.isZero_of_isStrictlyGE i (i - 1) (by omega)).eq_of_src _ _)
      have := P.isIso_iCycles i (i + 1) (by simp)
        ((P.isZero_of_isStrictlyLE i (i + 1) (by omega)).eq_of_tgt _ _)
      exact Module.Finite.equiv
        ((asIso (P.homologyπ i)).symm ≪≫ asIso (P.iCycles i)).toLinearEquiv
    · have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.1 <| by
        rcases lt_or_gt_of_ne hi with hi | hi
        · exact P.isZero_of_isStrictlyGE b i hi
        · exact P.isZero_of_isStrictlyLE b i hi
      infer_instance
  have := Module.finitePresentation_of_finite R (P.X i)
  exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

/-- The base case of the induction: an object of Tor amplitude in `[b, b]` with finitely
generated cohomology is represented by a finitely generated projective module in degree `b`. -/
private lemma hasProjectiveModelIn_of_torAmplitudeIn_self {b : ℤ}
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ b b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    HasProjectiveModelIn b b C := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hC
  refine ⟨P, inferInstance, inferInstance, projective_finite_of_flat P b hP ?_, ⟨e.symm⟩⟩
  have := hfin b
  exact Module.Finite.equiv
    ((homologyFunctor _ b).mapIso e.symm ≪≫ (homologyFunctorFactors _ b).app P).toLinearEquiv

/-- The induction step. Let `C` have Tor amplitude in `[c, b]` with `c < b` and finitely
generated cohomology. Represent `C` by a complex `P` of flat modules in degrees `[c, b]`, choose
a finite free module `F` mapping onto `H^b(C)` and lift it to a map `φ : F[-b] ⟶ P`. Its mapping
cone `C'` has Tor amplitude in `[c, b - 1]` and finitely generated cohomology, and if `C'` has a
projective model in degrees `[c, b - 1]`, then `C`, an extension of `C'` by `F[-b]`, has one in
degrees `[c, b]`. -/
private lemma exists_hasProjectiveModelIn_imp_of_torAmplitudeIn {c b : ℤ} (hcb : c < b)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    ∃ C' : DerivedCategory (ModuleCat.{u} R), torAmplitudeIn _ c (b - 1) C' ∧
      (∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C')) ∧
      (HasProjectiveModelIn c (b - 1) C' → HasProjectiveModelIn c b C) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hC
  let H (i : ℤ) := homologyFunctor (ModuleCat.{u} R) i
  let eH (L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
      (H i).obj (Q.obj L) ≅ L.homology i :=
    (homologyFunctorFactors _ i).app L
  have hPfin (i : ℤ) : Module.Finite R (P.homology i) := by
    have := hfin i
    exact Module.Finite.equiv ((H i).mapIso e.symm ≪≫ eH P i).toLinearEquiv
  -- a finite free module `F` mapping onto `H^b(P)`, lifted to the cycles of `P` in degree `b`
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (P.homology b)
  have hπ : Function.Surjective (P.homologyπ b).hom :=
    (ModuleCat.epi_iff_surjective _).1 inferInstance
  obtain ⟨h, hh⟩ := Module.projective_lifting_property (P.homologyπ b).hom g hπ
  let F := ModuleCat.of R (Fin n → R)
  let S : CochainComplex (ModuleCat.{u} R) ℤ :=
    (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) b).obj F
  let φ : S ⟶ P := HomologicalComplex.mkHomFromSingle (ModuleCat.ofHom h ≫ P.iCycles b)
    (by rintro k (rfl : b + 1 = k); simp)
  let K := CochainComplex.mappingCone φ
  let T := CochainComplex.mappingCone.triangle φ
  have hT : Q.mapTriangle.obj T ∈ distTriang _ := mappingCone_triangle_distinguished φ
  have hSX (i : ℤ) (hi : i ≠ b) : IsZero (S.X i) :=
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
  have hSproj (i : ℤ) : Module.Projective R (S.X i) ∧ Module.Finite R (S.X i) := by
    by_cases hi : i = b
    · subst hi
      let e' := (HomologicalComplex.singleObjXSelf (.up ℤ) i F).toLinearEquiv
      exact ⟨Module.Projective.of_equiv e'.symm, Module.Finite.equiv e'.symm⟩
    · have : Subsingleton (S.X i) := ModuleCat.isZero_iff_subsingleton.1 (hSX i hi)
      have : Module.Flat R (S.X i) :=
        (ModuleCat.flat_iff_flat _).1 (ObjectProperty.flat_of_isZero (hSX i hi))
      have := Module.finitePresentation_of_finite R (S.X i)
      exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩
  have hS : HasProjectiveModelIn b b (Q.obj S) :=
    ⟨S, inferInstance, inferInstance, hSproj, ⟨Iso.refl _⟩⟩
  -- the mapping cone is a complex of flat modules in degrees `[c, b]`
  have hKflat (i : ℤ) : ObjectProperty.flat (K.X i) := by
    have := (hSproj (i + 1)).1
    have := (ModuleCat.flat_iff_flat _).1 (hP i)
    exact (ModuleCat.flat_iff_flat _).2 (Module.Flat.of_linearEquiv
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl ≪≫
        ModuleCat.biprodIsoProd (S.X (i + 1)) (P.X i)).toLinearEquiv)
  have : K.IsStrictlyGE c := CochainComplex.isStrictlyGE_mappingCone φ b c c
  have : K.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨S.isZero_of_isStrictlyLE b _ (by omega), P.isZero_of_isStrictlyLE b _ (by omega)⟩
  -- `H^b(φ)` is surjective, so `H^b(K) = 0`
  have hepi : Epi (HomologicalComplex.homologyMap φ b) := by
    have : IsIso (S.iCycles b) := S.isIso_iCycles b (b + 1) (by simp)
      ((hSX (b + 1) (by omega)).eq_of_tgt _ _)
    have hc : HomologicalComplex.cyclesMap φ b = S.iCycles b ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) b F).hom ≫ ModuleCat.ofHom h := by
      rw [← cancel_mono (P.iCycles b), HomologicalComplex.cyclesMap_i]
      simp [φ, HomologicalComplex.mkHomFromSingle_f]
    have : Epi (ModuleCat.ofHom h ≫ P.homologyπ b) := by
      rw [ModuleCat.epi_iff_surjective]
      change Function.Surjective ((P.homologyπ b).hom ∘ₗ h)
      rw [hh]
      exact hg
    have : Epi (S.homologyπ b ≫ HomologicalComplex.homologyMap φ b) := by
      rw [HomologicalComplex.homologyπ_naturality, hc]
      simp only [Category.assoc]
      infer_instance
    exact epi_of_epi (S.homologyπ b) _
  have hKb : IsZero (K.homology b) :=
    (CochainComplex.homologyMap_exact₃_of_distTriang T hT b (b + 1)).isZero_X₂
      ((CochainComplex.homologyMap_exact₂_of_distTriang T hT b).epi_f_iff.1 hepi)
      (((S.exactAt_of_isLE b (b + 1) (by omega)).isZero_homology).eq_of_tgt _ _)
  have hKle : (Q.obj K).IsLE (b - 1) := by
    rw [isLE_Q_obj_iff, CochainComplex.isLE_iff]
    intro i hi
    obtain rfl | hi := eq_or_lt_of_le (show b ≤ i by omega)
    · exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hKb
    · exact K.exactAt_of_isLE b i hi
  have hK' : torAmplitudeIn _ c (b - 1) (Q.obj K) := fun N ↦ by
    refine ⟨(torAmplitudeIn_Q_obj_of_flat K c b hKflat N).1, ?_⟩
    have := isLE_tensor (Q.obj K) ((singleFunctor _ 0).obj N) (b - 1) 0
    rwa [add_zero] at this
  -- the cohomology of `K` is finitely generated
  have hKfin (i : ℤ) : Module.Finite R ((H i).obj (Q.obj K)) := by
    have : Module.Finite R (T.obj₂.homology i) := hPfin i
    have : Module.Finite R (T.obj₁.homology (i + 1)) := by
      have := (isPerfect_Q_obj S b b hSproj).finite_homology (i + 1)
      exact Module.Finite.equiv (eH S (i + 1)).toLinearEquiv
    have : Module.Finite R (K.homology i) :=
      (CochainComplex.homologyMap_exact₃_of_distTriang T hT i (i + 1)).moduleFinite_X₂
    exact Module.Finite.equiv (eH K i).toLinearEquiv.symm
  refine ⟨Q.obj K, hK', hKfin, fun hK ↦ ?_⟩
  exact ((hasProjectiveModelIn_obj₂_of_distTriang _ hT hS hK).of_iso e).mono
    (by omega) (by omega)

/-- Induction on the length `b - c` of the Tor amplitude. -/
private lemma hasProjectiveModelIn_of_torAmplitudeIn (n : ℕ) {c b : ℤ} (hcb : c ≤ b)
    (hn : b - c ≤ n) {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    HasProjectiveModelIn c b C := by
  induction n generalizing b C with
  | zero =>
    obtain rfl : c = b := by omega
    exact hasProjectiveModelIn_of_torAmplitudeIn_self hC hfin
  | succ n ih =>
    obtain rfl | hbc := eq_or_lt_of_le hcb
    · exact hasProjectiveModelIn_of_torAmplitudeIn_self hC hfin
    · obtain ⟨C', hC', hfin', himp⟩ :=
        exists_hasProjectiveModelIn_imp_of_torAmplitudeIn hbc hC hfin
      exact himp (ih (by omega) (by omega) hC' hfin')

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Bounded complexes of finite Tor amplitude
are perfect.

Let `R` be a Noetherian ring and `C` an object of `D(R)` with finitely generated cohomology
modules (over a Noetherian ring, this is a complex of finite `R`-modules) and Tor amplitude in
`[a, b]`, `a ≤ b`. Then `C` is isomorphic to the image of a complex of finitely generated
projective `R`-modules concentrated in degrees `[a, b]`. (Boundedness of `C` is implied by the
Tor amplitude condition.) -/
theorem exists_iso_Q_obj_projective_of_torAmplitudeIn {a b : ℤ} (hab : a ≤ b)
    {C : DerivedCategory (ModuleCat.{u} R)}
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C))
    (hC : torAmplitudeIn _ a b C) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P) :=
  hasProjectiveModelIn_of_torAmplitudeIn (b - a).toNat hab (by omega) hC hfin

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Bounded complexes of finite Tor amplitude
are perfect, local case.

Let `R` be a Noetherian local ring and `C` an object of `D(R)` with finitely generated
cohomology modules and Tor amplitude in `[a, b]`, `a ≤ b`. Then `C` is isomorphic to the image
of a complex of finite free `R`-modules concentrated in degrees `[a, b]`: over a local ring a
finitely generated projective module is free. -/
theorem exists_iso_Q_obj_free_of_torAmplitudeIn [IsLocalRing R] {a b : ℤ} (hab : a ≤ b)
    {C : DerivedCategory (ModuleCat.{u} R)}
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C))
    (hC : torAmplitudeIn _ a b C) :
    ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
      (∀ i, Module.Free R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P) := by
  obtain ⟨P, ha, hb, hP, e⟩ := exists_iso_Q_obj_projective_of_torAmplitudeIn hab hfin hC
  refine ⟨P, ha, hb, fun i ↦ ?_, e⟩
  have := (hP i).1
  have := (hP i).2
  exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩

end FiniteTorAmplitude

end DerivedCategory
