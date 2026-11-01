import Langlands.Cohomology.HyperextSecondPage
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# The abutment of the hyperext spectral sequence as cohomology of a Hom complex

Let `P` be a cochain complex in a preadditive category `C` and let `W` be an object of `C`.
The cochain complex of abelian groups `Hom(P^{-•}, W)` (`homObjComplex P W`) has the group
`P.X (-n) ⟶ W` in degree `n`, and its differentials are precomposition with the differentials
of `P`, without signs.

When `C` is abelian and `P` is K-projective, the cohomology of `homObjComplex P W` in degree `n`
is the group of morphisms `Q.obj P ⟶ W₀⟦n⟧` in the derived category, where `W₀` is `W` placed
in degree `0` (`homObjHomologyAddEquiv`). By Mathlib's `isKProjective_of_projective` this
applies to complexes that are strictly bounded above and have projective terms
(`homObjHomologyAddEquivOfProjective`). The group `Q.obj P ⟶ W₀⟦n⟧` is the term in degree `n`
of the hyperext spectral object of `Q.obj P` and `W₀` for the standard t-structure, the intended
abutment of the hyperext spectral sequence of `Langlands.Cohomology.HyperextSpectralSequence`
(`abutmentAddEquiv`).

The comparison goes through Mathlib's Hom complex `HomComplex P W₀`, whose differential has
signs. `homComplexSingleIso` identifies it with `homObjComplex P W`, multiplying the component
in degree `n` by `sign n = (-1)^{n(n+1)/2}`. Mathlib identifies the cohomology of `HomComplex P L`
with homotopy classes of morphisms `P ⟶ L⟦n⟧` (`HomComplex.homologyAddEquiv`,
`CohomologyClass.homAddEquiv`), and these with morphisms in the derived category when `P` is
K-projective (`IsKProjective.Qh_map_bijective`); `cohomologyClassAddEquiv` assembles them.
-/

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology

namespace HyperextHomComplex

universe w v u

section HomObj

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The cochain complex of abelian groups `Hom(P^{-•}, W)`: in degree `n` the group
`P.X (-n) ⟶ W`, with differential from degree `i` to degree `j` given by precomposition with
`P.d (-j) (-i)`. No signs are introduced. -/
def homObjComplex (P : CochainComplex C ℤ) (W : C) : CochainComplex AddCommGrpCat.{v} ℤ where
  X n := AddCommGrpCat.of (P.X (-n) ⟶ W)
  d i j := AddCommGrpCat.ofHom (Preadditive.leftComp W (P.d (-j) (-i)))
  shape i j hij := by
    ext f
    simp [Preadditive.leftComp, P.shape (-j) (-i) (by simp at hij ⊢; lia)]
  d_comp_d' i j k _ _ := by
    ext f
    simp [Preadditive.leftComp]

/-- The sign `(-1)^{n(n+1)/2}` relating Mathlib's Hom complex into a single complex with
`homObjComplex`. -/
def sign (n : ℤ) : ℤˣ := (n * (n + 1) / 2).negOnePow

lemma sign_succ (n : ℤ) : sign (n + 1) = sign n * (n + 1).negOnePow := by
  have h : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [sign, sign, h, Int.add_mul_ediv_right _ _ (by norm_num : (2 : ℤ) ≠ 0), Int.negOnePow_add]

lemma negOnePow_mul_sign_succ (n : ℤ) : (n + 1).negOnePow * sign (n + 1) = sign n := by
  rw [sign_succ, mul_comm (sign n), ← mul_assoc, Int.units_mul_self, one_mul]

variable [HasZeroObject C]

open CochainComplex HomComplex

/-- Cochains of degree `n` from `P` to `W` placed in degree `0`, identified with `P.X (-n) ⟶ W`
by Mathlib's `Cochain.toSingleEquiv` followed by multiplication by `sign n`. -/
noncomputable def cochainAddEquiv (P : CochainComplex C ℤ) (W : C) (n : ℤ) :
    Cochain P ((CochainComplex.singleFunctor C 0).obj W) n ≃+ (P.X (-n) ⟶ W) :=
  (Cochain.toSingleEquiv (neg_add_cancel n)).trans
    (DistribMulAction.toAddEquiv (P.X (-n) ⟶ W) (sign n))

lemma cochainAddEquiv_toSingleMk (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    (f : P.X (-n) ⟶ W) :
    cochainAddEquiv P W n (Cochain.toSingleMk f (neg_add_cancel n)) = sign n • f := by
  simp [cochainAddEquiv]

/-- Mathlib's Hom complex from `P` to `W` placed in degree `0` is isomorphic to
`homObjComplex P W`, with components `cochainAddEquiv`. -/
noncomputable def homComplexSingleIso (P : CochainComplex C ℤ) (W : C) :
    HomComplex P ((CochainComplex.singleFunctor C 0).obj W) ≅ homObjComplex P W :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (cochainAddEquiv P W n).toAddCommGrpIso)
    (by
      rintro i j (rfl : i + 1 = j)
      ext α
      obtain ⟨f, rfl⟩ := Cochain.toSingleMk_surjective α (-i) (neg_add_cancel i)
      change P.d (-(i + 1)) (-i) ≫ cochainAddEquiv P W i
          (Cochain.toSingleMk f (neg_add_cancel i)) =
        cochainAddEquiv P W (i + 1) (δ i (i + 1) (Cochain.toSingleMk f (neg_add_cancel i)))
      rw [Cochain.δ_toSingleMk f (neg_add_cancel i) (i + 1) (-(i + 1)) (neg_add_cancel (i + 1)),
        cochainAddEquiv_toSingleMk, Units.smul_def, Units.smul_def, map_zsmul,
        cochainAddEquiv_toSingleMk, Units.smul_def, Preadditive.comp_zsmul, smul_smul, ← Units.val_mul,
        negOnePow_mul_sign_succ])

end HomObj

section Derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory CochainComplex HomComplex HyperextSpectralSequence

/-- For a K-projective cochain complex `P`, cohomology classes of degree `n` of Mathlib's Hom
complex from `P` to `L` are morphisms `Q.obj P ⟶ (Q.obj L)⟦n⟧` in the derived category. -/
noncomputable def cohomologyClassAddEquiv (P L : CochainComplex C ℤ) (n : ℤ) [P.IsKProjective] :
    CohomologyClass P L n ≃+ (Q.obj P ⟶ (Q.obj L)⟦n⟧) :=
  (CohomologyClass.homAddEquiv (K := P) (L := L) (n := n)).trans <|
    (AddEquiv.ofBijective (Qh (C := C)).mapAddHom
      (IsKProjective.Qh_map_bijective P _)).trans <|
    (precompAddEquiv ((quotientCompQhIso C).app P).symm _).trans <|
    postcompAddEquiv _ ((quotientCompQhIso C).app (L⟦n⟧) ≪≫ (Q.commShiftIso n).app L)

/-- For a K-projective cochain complex `P`, the cohomology in degree `n` of Mathlib's Hom complex
from `P` to `L` is the group of morphisms `Q.obj P ⟶ (Q.obj L)⟦n⟧` in the derived category. -/
noncomputable def homComplexHomologyAddEquiv (P L : CochainComplex C ℤ) (n : ℤ)
    [P.IsKProjective] :
    (HomComplex P L).homology n ≃+ (Q.obj P ⟶ (Q.obj L)⟦n⟧) :=
  (HomComplex.homologyAddEquiv P L n).trans (cohomologyClassAddEquiv P L n)

/-- For a K-projective cochain complex `P` and `W : C`, the cohomology in degree `n` of the
complex `Hom(P^{-•}, W)` is the group of morphisms from `Q.obj P` to `W` placed in degree `0`
and shifted by `n`. -/
noncomputable def homObjHomologyAddEquiv (P : CochainComplex C ℤ) (W : C) (n : ℤ)
    [P.IsKProjective] :
    (homObjComplex P W).homology n ≃+ (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj W)⟦n⟧) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (homComplexSingleIso P W)).addCommGroupIsoToAddEquiv.symm.trans
    (homComplexHomologyAddEquiv P ((CochainComplex.singleFunctor C 0).obj W) n)

/-- The abutment in degree `n` of the hyperext spectral sequence of `Q.obj P` and `W` placed in
degree `0`, for the standard t-structure and a K-projective complex `P`, is the cohomology in
degree `n` of `Hom(P^{-•}, W)`. -/
noncomputable def abutmentAddEquiv (P : CochainComplex C ℤ) (W : C) (n : ℤ) [P.IsKProjective] :
    ((hyperextSpectralObject TStructure.t (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj W)).H n).obj
      (ComposableArrows.mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) ≃+
      (homObjComplex P W).homology n :=
  (abutmentIso TStructure.t (Q.obj P) ((DerivedCategory.singleFunctor C 0).obj W) n).addCommGroupIsoToAddEquiv.trans
    (homObjHomologyAddEquiv P W n).symm

/-- `homObjHomologyAddEquiv` for a complex `P` that is strictly bounded above by `d` and has
projective terms, which is K-projective by Mathlib's `isKProjective_of_projective`. -/
noncomputable def homObjHomologyAddEquivOfProjective (P : CochainComplex C ℤ) (W : C) (n d : ℤ)
    [P.IsStrictlyLE d] [∀ k, Projective (P.X k)] :
    (homObjComplex P W).homology n ≃+ (Q.obj P ⟶ ((DerivedCategory.singleFunctor C 0).obj W)⟦n⟧) :=
  haveI := isKProjective_of_projective P d
  homObjHomologyAddEquiv P W n

end Derived

end HyperextHomComplex

end Langlands.Cohomology
