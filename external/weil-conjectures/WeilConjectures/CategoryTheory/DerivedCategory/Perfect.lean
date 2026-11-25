/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.Plus
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Perfect complexes over a commutative ring

Let `R` be a commutative ring. An object `C` of the derived category `D(R)` is *perfect* if it
is isomorphic to the image of a bounded complex of finitely generated projective `R`-modules.
In the Poincaré duality chapter `R` is the coefficient ring of the point `s = Spec k`, and the
perfect objects of `D(R)` are the *perfect point complexes*.

## Main definitions

- `DerivedCategory.IsPerfect`: `C` is quasi-isomorphic to a bounded complex of finitely
  generated projective `R`-modules.

## Main statements

- `DerivedCategory.isPerfect_iff` (`corollary-degreewise-duality-over-fields--1`): over a field, `C`
  is perfect if and only if it is bounded with finite-dimensional cohomology.
- `DerivedCategory.IsPerfect.bounded`, `DerivedCategory.IsPerfect.finite_homology`: a perfect
  complex over a Noetherian ring is bounded with finitely generated cohomology.
- `DerivedCategory.isPerfect_of_finiteTorAmplitude` (`lemma-perfect-complexes-geometric-point`, Step
2): conversely, over a
  Noetherian ring a bounded complex with finitely generated cohomology and finite Tor amplitude
  is perfect.
- `DerivedCategory.IsPerfect.tensor_homology` (`lemma-perfect-complexes-geometric-point`, Step 3):
after a flat extension
  of scalars to a field the cohomology is finite dimensional and bounded.
- `DerivedCategory.IsPerfect.ihom_unit` (`lemma-perfect-complexes-geometric-point`, Step 3): the
dual
  `C^∨ = RHom_R(C, R)` of a perfect complex is perfect.
- `DerivedCategory.IsPerfect.isDualizable` (`lemma-perfect-complexes-geometric-point--8`, Steps
1–3): a
  perfect complex is dualizable for the derived tensor product.
- `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit` (`lemma-perfect-complexes-geometric-point--8`):
for
  any braiding of `D(R)`, the canonical biduality map `C ⟶ C^∨∨` is an isomorphism for a
  perfect `C`, where `C^∨ = RHom_R(C, R)`.
- `DerivedCategory.IsPerfect.isIso_ihomUnitTensorToIhom`
(`lemma-perfect-complexes-geometric-point--8`):
  the canonical comparison `C^∨ ⊗ᴸ_R D ⟶ RHom_R(C, D)` is an isomorphism for a perfect `C` and
  any `D`.
- `DerivedCategory.nonempty_iso_homology_ihom` (`corollary-degreewise-duality-over-fields--1`): over
  a field, `H^{-i}(C^∨) ≅ H^i(C)^∨`.

## Implementation notes

The biduality statements are deduced from the dualizability of a perfect complex for the
derived tensor product (`DerivedCategory.IsPerfect.isDualizable`), by the formal arguments of a
rigid braided monoidal category. The tensor–internal-Hom comparison needs no braiding and is
the canonical map `CategoryTheory.MonoidalClosed.ihomUnitTensorToIhom`. The canonical biduality
map `C ⟶ C^∨∨` needs a braiding. `D(R)` only carries one up to `Nonempty`
(`DerivedCategory.nonempty_braidedCategory`), so biduality is stated for an arbitrary braiding
instance; `DerivedCategory.IsPerfect.nonempty_iso_ihom_ihom` is the braiding-free consequence.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped TensorProduct

namespace DerivedCategory

variable {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Perfect complex of finite modules.

Also blueprint `sk-def-perfect` (also `lemma-perfect-complexes-geometric-point`): perfect point
complexes.

An object `C` of `D(R)` is *perfect* if it is isomorphic to the image of a bounded complex of
finitely generated projective `R`-modules. -/
def IsPerfect (C : DerivedCategory (ModuleCat.{u} R)) : Prop :=
  ∃ (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ), P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
    (∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) ∧ Nonempty (C ≅ Q.obj P)

/-- Perfectness is invariant under isomorphism. -/
theorem IsPerfect.of_iso {C D : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect)
    (e : C ≅ D) : D.IsPerfect := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e'⟩⟩ := hC
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ e'⟩⟩

/-- The cohomology of `Q.obj L` in degree `i` is that of the complex `L`. -/
private noncomputable def homologyQObjIso (L : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (homologyFunctor (ModuleCat.{u} R) i).obj (Q.obj L) ≅ L.homology i :=
  (homologyFunctorFactors _ i).app L

/-- A perfect complex is bounded: its cohomology is concentrated in some interval `[a, b]`. -/
theorem IsPerfect.exists_homologyConcentratedIn {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) : ∃ a b : ℤ, homologyConcentratedIn a b C := by
  obtain ⟨P, a, b, ha, hb, -, ⟨e⟩⟩ := hC
  let eH : ∀ i, (homologyFunctor (ModuleCat.{u} R) i).obj C ≅ P.homology i := fun i ↦
    (homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫ homologyQObjIso P i
  refine ⟨a, b, ?_, ?_⟩
  · change C.IsGE a
    rw [isGE_iff]
    intro i hi
    exact (P.exactAt_of_isGE a i hi).isZero_homology.of_iso (eH i)
  · change C.IsLE b
    rw [isLE_iff]
    intro i hi
    exact (P.exactAt_of_isLE b i hi).isZero_homology.of_iso (eH i)

/-- A perfect complex is bounded for the canonical t-structure. -/
theorem IsPerfect.bounded {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    TStructure.t.bounded C :=
  (exists_homologyConcentratedIn_iff_bounded C).1 hC.exists_homologyConcentratedIn

/-- The cohomology modules of a perfect complex over a Noetherian ring are finitely generated:
`H^i(P)` is a quotient of the submodule of cycles of the finitely generated module `P^i`. -/
theorem IsPerfect.finite_homology [IsNoetherianRing R] {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) (i : ℤ) :
    Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C) := by
  obtain ⟨P, a, b, -, -, hP, ⟨e⟩⟩ := hC
  let eH : (homologyFunctor (ModuleCat.{u} R) i).obj C ≅ P.homology i :=
    (homologyFunctor (ModuleCat.{u} R) i).mapIso e ≪≫ homologyQObjIso P i
  have := (hP i).2
  have : Module.Finite R (P.cycles i) :=
    Module.Finite.of_injective (P.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).1 inferInstance)
  have : Module.Finite R (P.homology i) :=
    Module.Finite.of_surjective (P.homologyπ i).hom
      ((ModuleCat.epi_iff_surjective _).1 inferInstance)
  exact Module.Finite.equiv eH.toLinearEquiv.symm

/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 3 of its proof): flat extension of
scalars to a field.

For a perfect complex `C` over a Noetherian ring `R` and an `R`-algebra `E` which is a field
(such as `E = Frac 𝒪_E` over `𝒪_E`), the spaces `E ⊗_R Hⁱ(C)` are finite dimensional and vanish
outside a finite interval. For `E` flat over `R` they are the cohomology spaces of
`C ⊗ᴸ_R E`, so this says that `C ⊗ᴸ_R E` is a perfect complex of `E`-vector spaces
(`DerivedCategory.isPerfect_iff`). -/
theorem IsPerfect.tensor_homology [IsNoetherianRing R] (E : Type*) [Field E] [Algebra R E]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    (∀ i, FiniteDimensional E (E ⊗[R] (homologyFunctor (ModuleCat.{u} R) i).obj C)) ∧
      ∃ a b : ℤ, ∀ i, i < a ∨ b < i →
        Subsingleton (E ⊗[R] (homologyFunctor (ModuleCat.{u} R) i).obj C) := by
  refine ⟨fun i ↦ have := hC.finite_homology i; inferInstance, ?_⟩
  obtain ⟨a, b, ha, hb⟩ := hC.exists_homologyConcentratedIn
  refine ⟨a, b, fun i hi ↦ ?_⟩
  have hz : IsZero ((homologyFunctor (ModuleCat.{u} R) i).obj C) := by
    rcases hi with hi | hi
    · exact C.isZero_of_isGE a i hi
    · exact C.isZero_of_isLE b i hi
  have := (ModuleCat.isZero_iff_subsingleton).1 hz
  refine subsingleton_of_forall_eq 0 fun x ↦ ?_
  induction x using TensorProduct.inductionOn with
  | tmul e m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/-- The image in `D(R)` of a bounded complex of finitely generated projective modules is
perfect. -/
lemma isPerfect_Q_obj (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) [P.IsStrictlyGE a]
    [P.IsStrictlyLE b] (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    (Q.obj P).IsPerfect :=
  ⟨P, a, b, inferInstance, inferInstance, hP, ⟨Iso.refl _⟩⟩

/-- Perfect complexes are stable under shifts. -/
lemma IsPerfect.shift {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) (n : ℤ) :
    (C⟦n⟧).IsPerfect := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  exact (isPerfect_Q_obj (P⟦n⟧) (a - n) (b - n) fun i ↦ hP (i + n)).of_iso
    (((Q.commShiftIso n).app P) ≪≫ (shiftFunctor _ n).mapIso e.symm)

/-- The mapping cone of a morphism between bounded complexes of finitely generated projective
modules is again such a complex. -/
lemma isPerfect_Q_obj_mappingCone {P₁ P₂ : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P₁ ⟶ P₂)
    (a₁ b₁ a₂ b₂ : ℤ) [P₁.IsStrictlyGE a₁] [P₁.IsStrictlyLE b₁] [P₂.IsStrictlyGE a₂]
    [P₂.IsStrictlyLE b₂] (h₁ : ∀ i, Module.Projective R (P₁.X i) ∧ Module.Finite R (P₁.X i))
    (h₂ : ∀ i, Module.Projective R (P₂.X i) ∧ Module.Finite R (P₂.X i)) :
    (Q.obj (CochainComplex.mappingCone φ)).IsPerfect := by
  have : (CochainComplex.mappingCone φ).IsStrictlyGE (min (a₁ - 1) a₂) :=
    CochainComplex.isStrictlyGE_mappingCone φ a₁ a₂ _
  have : (CochainComplex.mappingCone φ).IsStrictlyLE (max (b₁ - 1) b₂) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨P₁.isZero_of_isStrictlyLE b₁ _ (by omega), P₂.isZero_of_isStrictlyLE b₂ _ (by omega)⟩
  refine isPerfect_Q_obj _ (min (a₁ - 1) a₂) (max (b₁ - 1) b₂) fun i ↦ ?_
  let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl) ≪≫
    ModuleCat.biprodIsoProd (P₁.X (i + 1)) (P₂.X i)
  have := (h₁ (i + 1)).1
  have := (h₁ (i + 1)).2
  have := (h₂ i).1
  have := (h₂ i).2
  exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
    Module.Finite.equiv e.toLinearEquiv.symm⟩

/-- Perfect complexes are stable under extensions: in a distinguished triangle
`C₁ ⟶ C₂ ⟶ C₃ ⟶ C₁[1]` with `C₁` and `C₃` perfect, `C₂` is perfect. The map `C₃ ⟶ C₁[1]` lifts
to a morphism of complexes, its source being K-projective, and `C₂[1]` is its mapping cone. -/
lemma isPerfect_obj₂_of_distTriang
    (T : Pretriangulated.Triangle (DerivedCategory (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) (h₁ : T.obj₁.IsPerfect) (h₃ : T.obj₃.IsPerfect) :
    T.obj₂.IsPerfect := by
  obtain ⟨P₁, a₁, b₁, _, _, hP₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨P₃, a₃, b₃, _, _, hP₃, ⟨e₃⟩⟩ := h₃
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
  have hcone := isPerfect_Q_obj_mappingCone ψ a₃ b₃ (a₁ - 1) (b₁ - 1) hP₃ fun i ↦ hP₁ (i + 1)
  exact ((hcone.of_iso (Pretriangulated.Triangle.π₃.mapIso f)).shift (-1)).of_iso
    ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by omega)).app _)

section FiniteTorAmplitude

variable [IsNoetherianRing R]

/-- A complex of flat modules concentrated in degree `b`, whose cohomology in degree `b` is
finitely generated, has a perfect image in `D(R)`: its term in degree `b` is its cohomology, a
finitely presented flat module, hence projective. -/
private lemma isPerfect_Q_obj_of_flat (P : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
    [P.IsStrictlyGE b] [P.IsStrictlyLE b] (hP : ∀ n, ObjectProperty.flat (P.X n))
    (hb : Module.Finite R (P.homology b)) :
    (Q.obj P).IsPerfect := by
  refine isPerfect_Q_obj P b b fun i ↦ ?_
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

/-- The base case of `DerivedCategory.isPerfect_of_finiteTorAmplitude`: an object of Tor
amplitude in `[c, b]` with `b ≤ c` and finitely generated cohomology is perfect. It is
represented by a complex of flat modules concentrated in degree `b`. -/
private lemma isPerfect_of_torAmplitudeIn_of_le {c b : ℤ} (hbc : b ≤ c)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    C.IsPerfect := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := exists_iso_Q_obj_flat_of_torAmplitudeIn hC
  have : P.IsStrictlyGE b := CochainComplex.isStrictlyGE_of_ge P b c hbc
  refine (isPerfect_Q_obj_of_flat P b hP ?_).of_iso e
  have := hfin b
  exact Module.Finite.equiv
    ((homologyFunctor _ b).mapIso e.symm ≪≫ (homologyFunctorFactors _ b).app P).toLinearEquiv

/-- The induction step of `DerivedCategory.isPerfect_of_finiteTorAmplitude`. Let `C` have Tor
amplitude in `[c, b]` with `c < b` and finitely generated cohomology. Represent `C` by a complex
`P` of flat modules in degrees `[c, b]`, choose a finite free module `F` mapping onto
`H^b(C) = P^b / d(P^{b-1})` and lift it to a map `φ : F[-b] ⟶ P`. Its mapping cone `C'` is a
complex of flat modules in degrees `[c, b]` with `H^b(C') = 0`, so it has Tor amplitude in
`[c, b - 1]`, and its cohomology is finitely generated. If `C'` is perfect, so is `C`, as an
extension of `C'` by the perfect complex `F[-b]`. -/
private lemma exists_isPerfect_imp_of_torAmplitudeIn {c b : ℤ} (hcb : c < b)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    ∃ C' : DerivedCategory (ModuleCat.{u} R), torAmplitudeIn _ c (b - 1) C' ∧
      (∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C')) ∧
      (C'.IsPerfect → C.IsPerfect) := by
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
  have hS : (Q.obj S).IsPerfect := isPerfect_Q_obj S b b fun i ↦ by
    by_cases hi : i = b
    · subst hi
      let e' := (HomologicalComplex.singleObjXSelf (.up ℤ) i F).toLinearEquiv
      exact ⟨Module.Projective.of_equiv e'.symm, Module.Finite.equiv e'.symm⟩
    · have : Subsingleton (S.X i) := ModuleCat.isZero_iff_subsingleton.1 (hSX i hi)
      have : Module.Flat R (S.X i) :=
        (ModuleCat.flat_iff_flat _).1 (ObjectProperty.flat_of_isZero (hSX i hi))
      have := Module.finitePresentation_of_finite R (S.X i)
      exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩
  -- the mapping cone is a complex of flat modules in degrees `[c, b]`
  have hSflat (i : ℤ) : Module.Flat R (S.X i) := by
    by_cases hi : i = b
    · subst hi
      exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXSelf (.up ℤ) i F).toLinearEquiv
    · exact (ModuleCat.flat_iff_flat _).1 (ObjectProperty.flat_of_isZero (hSX i hi))
  have hKflat (i : ℤ) : ObjectProperty.flat (K.X i) := by
    have := hSflat (i + 1)
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
      have := hS.finite_homology (i + 1)
      exact Module.Finite.equiv (eH S (i + 1)).toLinearEquiv
    have : Module.Finite R (K.homology i) :=
      (CochainComplex.homologyMap_exact₃_of_distTriang T hT i (i + 1)).moduleFinite_X₂
    exact Module.Finite.equiv (eH K i).toLinearEquiv.symm
  exact ⟨Q.obj K, hK', hKfin, fun hK ↦ (isPerfect_obj₂_of_distTriang _ hT hS hK).of_iso e⟩

/-- Induction on the length `b - c` of the Tor amplitude: an object of Tor amplitude in `[c, b]`
with finitely generated cohomology is perfect. -/
private lemma isPerfect_of_torAmplitudeIn (n : ℕ) {c b : ℤ} (hn : b - c ≤ n)
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : torAmplitudeIn _ c b C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C)) :
    C.IsPerfect := by
  induction n generalizing b C with
  | zero => exact isPerfect_of_torAmplitudeIn_of_le (by omega) hC hfin
  | succ n ih =>
    by_cases hbc : b ≤ c
    · exact isPerfect_of_torAmplitudeIn_of_le hbc hC hfin
    · obtain ⟨C', hC', hfin', himp⟩ := exists_isPerfect_imp_of_torAmplitudeIn (by omega) hC hfin
      exact himp (ih (by omega) hC' hfin')

end FiniteTorAmplitude

/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 2 of its proof): perfectness over a
Noetherian ring.

Over a Noetherian ring `R`, a bounded complex `C` with finitely generated cohomology modules and
finite Tor amplitude is perfect. The proof is by induction on the length of the Tor amplitude
`[c, b]`. If `b ≤ c`, then `C` is represented by a complex of flat modules concentrated in
degree `b`, whose term is finitely presented and flat, hence projective. Otherwise a finite free
module `F` maps onto `H^b(C)`, and the cone of the lifted map `F[-b] ⟶ C` has Tor amplitude in
`[c, b - 1]` and finitely generated cohomology; `C` is an extension of it by `F[-b]`. The
boundedness hypothesis is implied by the finite Tor amplitude. -/
theorem isPerfect_of_finiteTorAmplitude [IsNoetherianRing R]
    {C : DerivedCategory (ModuleCat.{u} R)} (_hC : TStructure.t.bounded C)
    (hfin : ∀ i, Module.Finite R ((homologyFunctor (ModuleCat.{u} R) i).obj C))
    (hTor : finiteTorAmplitude (ModuleCat.{u} R) C) : C.IsPerfect := by
  obtain ⟨c, d, hcd⟩ := hTor
  exact isPerfect_of_torAmplitudeIn (d - c).toNat (by omega) hcd hfin

/-- Blueprint `lemma-perfect-complexes-geometric-point` (Step 3 of its proof): the dual of a perfect
point complex.

The dual `C^∨ = RHom_R(C, R)` of a perfect complex `C` is perfect: if `C` is represented by a
bounded complex `P` of finitely generated projective modules, `C^∨` is represented by the
termwise dual complex `Hom_R(P^{-i}, R)`, again bounded with finitely generated projective
terms. -/
theorem IsPerfect.ihom_unit {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    ((ihom C).obj (𝟙_ _)).IsPerfect := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  have hd (n : ℤ) : IsDualizable (P.X n) := by
    have := (hP n).1
    have := (hP n).2
    exact ModuleCat.isDualizable_of_projective (P.X n)
  let _ : ∀ n, HasRightDual (P.X n) := fun n ↦ (hd n).some
  have hD (n : ℤ) : Module.Projective R (P.rightDual.X n) ∧
      Module.Finite R (P.rightDual.X n) := by
    have := (hP (-n)).1
    have := (hP (-n)).2
    let f : P.rightDual.X n ≅ ModuleCat.of R (Module.Dual R (P.X (-n))) :=
      (ihomUnitIsoRightDual (P.X (-n))).symm ≪≫
        (ModuleCat.homLinearEquiv (S := R)).toModuleIso
    exact ⟨Module.Projective.of_equiv f.toLinearEquiv.symm,
      Module.Finite.equiv f.toLinearEquiv.symm⟩
  let _ := CochainComplex.exactPairingRightDual P a b
  let H := HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)
  have hd' (n : ℤ) : IsDualizable (P.rightDual.X n) :=
    ⟨{ rightDual := P.X (-n)
       exact := (BraidedCategory.exactPairing_swap (P.X (-n)) (P.X (-n))ᘁ :) }⟩
  let X : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P a b (fun n ↦ (hd n).flat))⟩
  let Y : (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat.FullSubcategory :=
    ⟨H.obj P.rightDual, (HomotopyCategory.kFlat_quotient_obj_iff _).2
      (CochainComplex.kFlat_of_bounded_of_flat P.rightDual (-b) (-a)
        (fun n ↦ (hd' n).flat))⟩
  let _ : ExactPairing ((ObjectProperty.ι _).obj X) ((ObjectProperty.ι _).obj Y) :=
    ExactPairing.map H P P.rightDual
  let _ : ExactPairing X Y := ExactPairing.ofFullyFaithful (ObjectProperty.ι _) X Y
  let _ := Functor.Monoidal.ofLaxMonoidal (kFlatQh (ModuleCat.{u} R))
  let _ : ExactPairing ((kFlatQh (ModuleCat.{u} R)).obj X)
      ((kFlatQh (ModuleCat.{u} R)).obj Y) :=
    ExactPairing.map (kFlatQh (ModuleCat.{u} R)) X Y
  let _ : HasRightDual ((kFlatQh (ModuleCat.{u} R)).obj X) :=
    ⟨(kFlatQh (ModuleCat.{u} R)).obj Y⟩
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let f : (ihom C).obj (𝟙_ _) ≅ Q.obj P.rightDual :=
    (MonoidalClosed.internalHom.mapIso
      ((quotientCompQhIso _).app P ≪≫ e.symm).op).app _ ≪≫
      ihomUnitIsoRightDual ((kFlatQh (ModuleCat.{u} R)).obj X) ≪≫
      (quotientCompQhIso _).app P.rightDual
  exact (isPerfect_Q_obj P.rightDual (-b) (-a) hD).of_iso f.symm

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
/-- A complex of modules whose cohomology modules are projective (for example any complex over a
semisimple ring, such as a field) is quasi-isomorphic to the complex of its cohomology modules
with zero differential: a choice of sections of the surjections `Z^i(L) ↠ H^i(L)` defines a
quasi-isomorphism from the latter to `L`. -/
theorem exists_quasiIso_of_zero_differential_of_projective
    (L : CochainComplex (ModuleCat.{u} R) ℤ) (hL : ∀ i, Module.Projective R (L.homology i)) :
    ∃ (H : CochainComplex (ModuleCat.{u} R) ℤ) (φ : H ⟶ L), QuasiIso φ ∧ (∀ i j, H.d i j = 0) ∧
      ∀ i, Nonempty (H.X i ≅ L.homology i) := by
  have hs : ∀ i, ∃ s : L.homology i ⟶ L.cycles i, s ≫ L.homologyπ i = 𝟙 _ := fun i ↦ by
    have hπ : Function.Surjective (L.homologyπ i).hom :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have := hL i
    obtain ⟨g, hg⟩ := Module.projective_lifting_property (L.homologyπ i).hom LinearMap.id hπ
    exact ⟨ModuleCat.ofHom g, ModuleCat.hom_ext hg⟩
  choose s hs using hs
  let H : CochainComplex (ModuleCat.{u} R) ℤ :=
    { X := fun i ↦ L.homology i
      d := fun _ _ ↦ 0 }
  let φ : H ⟶ L :=
    { f := fun i ↦ s i ≫ L.iCycles i }
  refine ⟨H, φ, ⟨fun i ↦ ?_⟩, fun _ _ ↦ rfl, fun i ↦ ⟨Iso.refl _⟩⟩
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₁ := H.isIso_homologyπ (i - 1) i (by simp) rfl
  have h₂ := H.isIso_iCycles i (i + 1) (by simp) rfl
  have hc : HomologicalComplex.cyclesMap φ i = H.iCycles i ≫ s i := by
    rw [← cancel_mono (L.iCycles i), HomologicalComplex.cyclesMap_i, Category.assoc]
  have : HomologicalComplex.homologyMap φ i = inv (H.homologyπ i) ≫ H.iCycles i := by
    rw [← cancel_epi (H.homologyπ i), HomologicalComplex.homologyπ_naturality, hc,
      Category.assoc, hs, Category.comp_id, IsIso.hom_inv_id_assoc]
  rw [this]
  infer_instance

omit [HasDerivedCategory.{u} (ModuleCat.{u} R)] in
/-- A complex of modules over a semisimple ring (for example a field) is quasi-isomorphic to the
complex of its cohomology modules with zero differential. -/
theorem exists_quasiIso_of_zero_differential [IsSemisimpleRing R]
    (L : CochainComplex (ModuleCat.{u} R) ℤ) :
    ∃ (H : CochainComplex (ModuleCat.{u} R) ℤ) (φ : H ⟶ L), QuasiIso φ ∧ (∀ i j, H.d i j = 0) ∧
      ∀ i, Nonempty (H.X i ≅ L.homology i) :=
  exists_quasiIso_of_zero_differential_of_projective L fun i ↦
    Module.projective_of_isSemisimpleRing R (L.homology i)

section Field

variable {K : Type u} [Field K] [HasDerivedCategory.{u} (ModuleCat.{u} K)]

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: perfect point complexes over a field.

Over a field `K`, an object `C` of `D(K)` is perfect if and only if it is bounded and all its
cohomology spaces `H^i(C)` are finite dimensional over `K`. -/
theorem isPerfect_iff (C : DerivedCategory (ModuleCat.{u} K)) :
    C.IsPerfect ↔ (∃ a b : ℤ, C.IsGE a ∧ C.IsLE b) ∧
      ∀ i, Module.Finite K ((homologyFunctor (ModuleCat.{u} K) i).obj C) := by
  constructor
  · rintro ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩
    let eH : ∀ i, (homologyFunctor (ModuleCat.{u} K) i).obj C ≅ P.homology i := fun i ↦
      (homologyFunctor (ModuleCat.{u} K) i).mapIso e ≪≫ homologyQObjIso P i
    refine ⟨⟨a, b, ?_, ?_⟩, fun i ↦ ?_⟩
    · rw [isGE_iff]
      intro i hi
      exact (P.exactAt_of_isGE a i hi).isZero_homology.of_iso (eH i)
    · rw [isLE_iff]
      intro i hi
      exact (P.exactAt_of_isLE b i hi).isZero_homology.of_iso (eH i)
    · have := (hP i).2
      have : Module.Finite K (P.cycles i) :=
        Module.Finite.of_injective (P.iCycles i).hom
          ((ModuleCat.mono_iff_injective _).1 inferInstance)
      have : Module.Finite K (P.homology i) :=
        Module.Finite.of_surjective (P.homologyπ i).hom
          ((ModuleCat.epi_iff_surjective _).1 inferInstance)
      exact Module.Finite.equiv (eH i).toLinearEquiv.symm
  · rintro ⟨⟨a, b, ha, hb⟩, hfin⟩
    let L := Q.objPreimage C
    let eL : Q.obj L ≅ C := Q.objObjPreimageIso C
    obtain ⟨H, φ, hφ, -, eH⟩ := exists_quasiIso_of_zero_differential L
    let e : ∀ i, (homologyFunctor (ModuleCat.{u} K) i).obj C ≅ H.X i := fun i ↦
      (homologyFunctor (ModuleCat.{u} K) i).mapIso eL.symm ≪≫ homologyQObjIso L i ≪≫
        (eH i).some.symm
    refine ⟨H, a, b, ?_, ?_, fun i ↦ ⟨?_, ?_⟩, ?_⟩
    · rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact (C.isZero_of_isGE a i hi).of_iso (e i).symm
    · rw [CochainComplex.isStrictlyLE_iff]
      intro i hi
      exact (C.isZero_of_isLE b i hi).of_iso (e i).symm
    · exact Module.Projective.of_free
    · exact Module.Finite.equiv (e i).toLinearEquiv
    · have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} K) φ).2 hφ
      exact ⟨eL.symm ≪≫ (asIso (Q.map φ)).symm⟩

end Field

section Biduality

/-- Blueprint `lemma-perfect-complexes-geometric-point--8` (Steps 1–3 of its proof): a perfect point
complex is dualizable for the derived tensor product of `D(R)`.

A finitely generated projective module is dualizable, with dual `Hom_R(P, R)`
(`ModuleCat.isDualizable_of_projective`). A bounded complex `P` of such modules is paired with
its termwise dual complex for the tensor product of complexes, and `P` and its dual are K-flat,
so the pairing descends to `D(R)` (`DerivedCategory.isDualizable_Q_obj`). This replaces the
blueprint's induction along the truncation triangles by a direct chain-level construction of the
evaluation and coevaluation. Dualizability is invariant under isomorphism. -/
theorem IsPerfect.isDualizable {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    IsDualizable C := by
  obtain ⟨P, a, b, _, _, hP, ⟨e⟩⟩ := hC
  refine IsDualizable.of_iso e.symm (isDualizable_Q_obj P a b fun n ↦ ?_)
  have := (hP n).1
  have := (hP n).2
  exact ModuleCat.isDualizable_of_projective (P.X n)

/-- Blueprint `lemma-perfect-complexes-geometric-point--8`: biduality at the point.

For a perfect point complex `C` and any braiding of `D(R)`, the canonical biduality map
`C ⟶ C^∨∨`, where `C^∨ = RHom_R(C, R)`, is an isomorphism. This is also clause (3) of blueprint
`lemma-perfect-complexes-geometric-point--8`: derived evaluation into the coefficient double dual is
an isomorphism for every perfect complex over any ring. -/
theorem IsPerfect.isIso_toIhomIhomUnit [BraidedCategory (DerivedCategory (ModuleCat.{u} R))]
    {C : DerivedCategory (ModuleCat.{u} R)} (hC : C.IsPerfect) :
    IsIso (MonoidalClosed.toIhomIhomUnit C) :=
  MonoidalClosed.isIso_toIhomIhomUnit_of_isDualizable hC.isDualizable

/-- Biduality at the point without a chosen braiding: a perfect point complex `C` is isomorphic
to its double derived dual `C^∨∨`. This only asserts that some isomorphism exists; it is the
biduality map of `DerivedCategory.IsPerfect.isIso_toIhomIhomUnit` for a braiding of `D(R)`, of
which only the existence is known (`DerivedCategory.nonempty_braidedCategory`). -/
theorem IsPerfect.nonempty_iso_ihom_ihom {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) :
    Nonempty (C ≅ (ihom ((ihom C).obj (𝟙_ _))).obj (𝟙_ _)) := by
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  have := hC.isIso_toIhomIhomUnit
  exact ⟨asIso (MonoidalClosed.toIhomIhomUnit C)⟩

/-- Blueprint `lemma-perfect-complexes-geometric-point--8`: biduality at the point.

For a perfect point complex `C` and every object `D` of `D(R)`, the canonical tensor–internal-Hom
comparison `C^∨ ⊗ᴸ_R D ⟶ RHom_R(C, D)` is an isomorphism. -/
theorem IsPerfect.isIso_ihomUnitTensorToIhom {C : DerivedCategory (ModuleCat.{u} R)}
    (hC : C.IsPerfect) (D : DerivedCategory (ModuleCat.{u} R)) :
    IsIso (MonoidalClosed.ihomUnitTensorToIhom C D) := by
  obtain ⟨_⟩ := hC.isDualizable
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let := BraidedCategory.exactPairing_swap C Cᘁ
  exact MonoidalClosed.isIso_ihomUnitTensorToIhom Cᘁ C D

end Biduality

section CohomologyDual

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: cohomology of the dual of a finite
complex over a field.

Over a field `R`, the cohomology of the dual `C^∨ = RHom_R(C, R)` of a complex `C` is the dual
of the cohomology: `H^{-i}(C^∨) ≅ H^i(C)^∨` for every `i`. The blueprint states this for a
perfect point complex `C` (a bounded complex of finite-dimensional vector spaces); it holds for
every `C`. Biduality `C ≅ C^∨∨` for perfect `C`, the other half of the node, is
`DerivedCategory.IsPerfect.isIso_toIhomIhomUnit`.

As in the blueprint, `C` is split: it is quasi-isomorphic to the complex `H` of its cohomology
spaces with zero differential. The single complex `R[0]` is K-injective, `R` being an injective
`R`-module, so `C^∨` is computed by the internal hom complex `Hom^•(H, R[0])`, which has zero
differential and the dual `Hom_R(H^i(C), R)` in degree `-i`.

The field is a commutative ring `R` with `IsField R`, so that the statement applies to the module
categories of the coefficient rings of the six-functor formalism, which are commutative
rings. -/
theorem nonempty_iso_homology_ihom (hR : IsField R) (C : DerivedCategory (ModuleCat.{u} R))
    (i : ℤ) :
    Nonempty ((homologyFunctor (ModuleCat.{u} R) (-i)).obj ((ihom C).obj (𝟙_ _)) ≅
      ModuleCat.of R (Module.Dual R ((homologyFunctor (ModuleCat.{u} R) i).obj C))) := by
  have : IsSemisimpleRing R := by
    let := hR.toField
    infer_instance
  obtain ⟨H, φ, hφ, hd, eH⟩ := exists_quasiIso_of_zero_differential (Q.objPreimage C)
  let P := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj H
  -- The unit `R[0]` of `D(R)`, a K-injective complex.
  let Y := (HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj
    (ModuleCat.of R R)
  have hY : ∀ n, n ≠ 0 → IsZero (Y.X n) := fun n hn ↦
    HomologicalComplex.isZero_single_obj_X _ _ _ _ hn
  have : ∀ n, Injective (Y.X n) := fun n ↦ by
    by_cases hn : n = 0
    · subst hn
      have := Module.injective_of_isSemisimpleRing R R
      exact Injective.of_iso (HomologicalComplex.singleObjXSelf _ 0 (ModuleCat.of R R)).symm
        (Module.injective_object_of_injective_module R R)
    · exact (hY n hn).injective
  have : CochainComplex.IsKInjective Y := CochainComplex.isKInjective_of_injective Y 0
  have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} R) φ).2 hφ
  let eC : Qh.obj P ≅ C :=
    (quotientCompQhIso _).app H ≪≫ asIso (Q.map φ) ≪≫ Q.objObjPreimageIso C
  let U := (HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)).obj Y
  -- `C^∨` is computed by the internal hom complex `K = Hom^•(H, R[0])`.
  let K := CochainComplex.internalHomObj H Y
  let e₁ : (ihom C).obj (𝟙_ _) ≅ Q.obj K :=
    (MonoidalClosed.internalHom.mapIso eC.op).app _ ≪≫
      ((ihom.adjunction (Qh.obj P)).rightAdjointUniq (tensorHomAdjunctionQhObj P)).app _ ≪≫
      (asIso ((internalHomQhObjUnit P).app U)).symm ≪≫ (quotientCompQhIso _).app K
  have hK : ∀ a b, K.d a b = 0 := fun a b ↦ by
    refine CochainComplex.internalHomObj_hom_ext fun p q hpq ↦ ?_
    rw [zero_comp, CochainComplex.internalHomObj_d_π H Y a b p q hpq (p + a) (q - a) rfl
      (by lia), hd]
    simp [Y]
  let e₂ : K.homology (-i) ≅ K.X (-i) :=
    (K.isoHomologyπ (-i - 1) (-i) (by simp) (hK _ _)).symm ≪≫
      K.iCyclesIso (-i) (-i + 1) (by simp) (hK _ _)
  -- In degree `-i`, the only nonzero factor of `K` is `Hom(H^i, R)`.
  let j₀ : CochainComplex.HomComplex.Triplet (-i) := ⟨i, 0, by lia⟩
  let e₃ : K.X (-i) ≅ (ihom (H.X i)).obj (ModuleCat.of R R) :=
    (by classical exact Pi.isoOfIsZero _ j₀ (fun T hT ↦ by
      have hq : T.q ≠ 0 := by
        intro hq
        apply hT
        obtain ⟨p, q, hpq⟩ := T
        simp only at hq
        subst hq
        obtain rfl : p = i := by lia
        rfl
      exact Functor.map_isZero _ (hY _ hq))) ≪≫
      (ihom (H.X i)).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (ModuleCat.of R R))
  let f : H.X i ≅ (homologyFunctor (ModuleCat.{u} R) i).obj C :=
    (eH i).some ≪≫ ((homologyFunctorFactors _ i).app _).symm ≪≫
      (homologyFunctor (ModuleCat.{u} R) i).mapIso (Q.objObjPreimageIso C)
  exact ⟨(homologyFunctor (ModuleCat.{u} R) (-i)).mapIso e₁ ≪≫
    (homologyFunctorFactors _ (-i)).app K ≪≫ e₂ ≪≫ e₃ ≪≫
    (ModuleCat.homLinearEquiv (S := R)).toModuleIso ≪≫
    (f.symm.toLinearEquiv.dualMap).toModuleIso⟩

/-- Cohomology of the dual of a complex with projective cohomology. If `C` is bounded and its
cohomology modules `Hʲ(C)` are finitely generated projective `R`-modules, then the cohomology of
the dual `C^∨ = RHom_R(C, R)` is the dual of the cohomology: `H^{-i}(C^∨) ≅ Hom_R(H^i(C), R)`.
This is the form of `DerivedCategory.nonempty_iso_homology_ihom` over a ring which is not a
field, used for the degreewise duality at the integral stage `𝒪_E`
(`prop-pod-integral-degreewise-form`).

As over a field, `C` is split: it is quasi-isomorphic to the bounded complex `H` of its
cohomology modules with zero differential
(`DerivedCategory.exists_quasiIso_of_zero_differential_of_projective`), whose dual is the
termwise dual complex, again with zero differential. -/
theorem nonempty_iso_homology_ihom_of_projective {C : DerivedCategory (ModuleCat.{u} R)}
    {a b : ℤ} (ha : C.IsGE a) (hb : C.IsLE b)
    (hC : ∀ j, Module.Projective R ((homologyFunctor (ModuleCat.{u} R) j).obj C) ∧
      Module.Finite R ((homologyFunctor (ModuleCat.{u} R) j).obj C)) (i : ℤ) :
    Nonempty ((homologyFunctor (ModuleCat.{u} R) (-i)).obj ((ihom C).obj (𝟙_ _)) ≅
      ModuleCat.of R (Module.Dual R ((homologyFunctor (ModuleCat.{u} R) i).obj C))) := by
  let L := Q.objPreimage C
  let eL : Q.obj L ≅ C := Q.objObjPreimageIso C
  let fL : ∀ j, L.homology j ≅ (homologyFunctor (ModuleCat.{u} R) j).obj C := fun j ↦
    ((homologyFunctorFactors _ j).app L).symm ≪≫ (homologyFunctor _ j).mapIso eL
  obtain ⟨H, φ, hφ, hd, eH⟩ := exists_quasiIso_of_zero_differential_of_projective L fun j ↦
    have := (hC j).1
    Module.Projective.of_equiv (fL j).toLinearEquiv.symm
  let gH : ∀ j, H.X j ≅ (homologyFunctor (ModuleCat.{u} R) j).obj C := fun j ↦
    (eH j).some ≪≫ fL j
  have hH : ∀ j, Module.Projective R (H.X j) ∧ Module.Finite R (H.X j) := fun j ↦
    have := (hC j).1
    have := (hC j).2
    ⟨Module.Projective.of_equiv (gH j).toLinearEquiv.symm,
      Module.Finite.equiv (gH j).toLinearEquiv.symm⟩
  have : H.IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro j hj
    exact ((C.isGE_iff a).1 ha j hj).of_iso (gH j)
  have : H.IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact ((C.isLE_iff b).1 hb j hj).of_iso (gH j)
  have : IsIso (Q.map φ) := (isIso_Q_map_iff_quasiIso (C := ModuleCat.{u} R) φ).2 hφ
  let eC : C ≅ Q.obj H := (asIso (Q.map φ) ≪≫ eL).symm
  let _ (n : ℤ) : HasRightDual (H.X n) :=
    have := (hH n).1
    have := (hH n).2
    (ModuleCat.isDualizable_of_projective (H.X n)).some
  obtain ⟨_⟩ := nonempty_exactPairing_Q_obj H a b
  obtain ⟨_⟩ := nonempty_braidedCategory (ModuleCat.{u} R)
  let _ := BraidedCategory.exactPairing_swap (Q.obj H) (Q.obj H.rightDual)
  let _ : ExactPairing (Q.obj H.rightDual) C := exactPairingCongrRight eC
  have hd' : ∀ p q, H.rightDual.d p q = 0 := fun p q ↦ by
    rw [CochainComplex.rightDual_d, hd]
    simp [rightAdjointMate]
  let e₂ : H.rightDual.homology (-i) ≅ H.rightDual.X (-i) :=
    (H.rightDual.isoHomologyπ (-i - 1) (-i) (by simp) (hd' _ _)).symm ≪≫
      H.rightDual.iCyclesIso (-i) (-i + 1) (by simp) (hd' _ _)
  have := (hH (-(-i))).1
  have := (hH (-(-i))).2
  let e₃ : H.rightDual.X (-i) ≃ₗ[R] Module.Dual R (H.X (-(-i))) :=
    (ihomUnitIsoRightDual (H.X (-(-i)))).toLinearEquiv.symm ≪≫ₗ ModuleCat.homLinearEquiv
  exact ⟨(homologyFunctor (ModuleCat.{u} R) (-i)).mapIso
      (MonoidalClosed.ihomObjUnitIso (Q.obj H.rightDual) C) ≪≫
    (homologyFunctorFactors _ (-i)).app _ ≪≫ e₂ ≪≫
    (e₃ ≪≫ₗ ((H.XIsoOfEq (neg_neg i)) ≪≫ gH i).toLinearEquiv.symm.dualMap).toModuleIso⟩

end CohomologyDual

end DerivedCategory
