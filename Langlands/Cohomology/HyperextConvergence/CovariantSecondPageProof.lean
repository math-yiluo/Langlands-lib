import Langlands.Cohomology.HyperextConvergence.HalfBoundedStatement
import Langlands.Cohomology.HyperextSecondPage

/-!
# The covariant hyperext spectral sequence: second page and abutment

Let `C` be an abelian category with a model of its derived category `D(C)`, let `K` be an object
of `D(C)` and `A` an object of `C`, and write `A₀` for `A` placed in degree `0`. This module
proves `CovariantSecondPageStatement`: for the hyperext spectral sequence, in `D(C)ᵒᵖ` with the
opposite `tOp` of the standard t-structure, of `op K` and `op A₀`,

* the object in position `(p, q)` on page 2 is `Ext^p(A, H^q(K))` for `p : ℕ`
  (`secondPageAddEquiv`);
* it is zero for `p < 0` (`isZero_secondPage_of_neg`);
* the abutment `op K ⟶ (op A₀)⟦n⟧` is `ShiftedHom A₀ K n` (`abutmentAddEquiv`).

The main step is an isomorphism `coheartPieceIso K q` from the object `coheartPiece K q` of
`D(C)` underlying `heartPiece tOp (op K) q` to `H^q(K)` placed in degree `q`. It dualizes Worker
61's `heartPieceIso` (module `Langlands.Cohomology.HyperextSecondPage`): the generic truncation
triangles `upperTriangle` and `heartTriangle` of that module, for `tOp` on `D(C)ᵒᵖ`, are turned
into distinguished triangles of `D(C)` by Mathlib's `unop_distinguished` (`coupperTriangle`,
`coheartTriangle`); their long exact cohomology sequences show that the maps
`upperPiece.unop ⟶ K` and `upperPiece.unop ⟶ coheartPiece K q` induce isomorphisms on `H^q`;
and `coheartPiece K q`, lying in degrees `≥ q` and `≤ q`, is isomorphic to `H^q` of itself
placed in degree `q` (`isoSingleHomology`).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  CategoryTheory.Pretriangulated.Opposite CategoryTheory.Triangulated Opposite

namespace Langlands.Cohomology

namespace HyperextConvergence

namespace CovariantSecondPage

open HyperextSpectralSequence

section Generic

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Passing to the opposite category, as an additive equivalence
`(X ⟶ Y) ≃+ (Y.unop ⟶ X.unop)`, `f ↦ f.unop`. -/
def unopAddEquiv (X Y : Cᵒᵖ) : (X ⟶ Y) ≃+ (Y.unop ⟶ X.unop) where
  toFun f := f.unop
  invFun g := g.op
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

end Generic

section Derived

universe w' w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open DerivedCategory

/-- The opposite of the standard t-structure, on the opposite of the derived category. -/
abbrev tOp : TStructure (DerivedCategory C)ᵒᵖ :=
  opTStructure (TStructure.t : TStructure (DerivedCategory C))

/-- The object of the derived category underlying `heartPiece tOp (op K) q`; classically the
truncation `τ_{≥ q} τ_{≤ q} K`. -/
abbrev coheartPiece (K : DerivedCategory C) (q : ℤ) : DerivedCategory C :=
  (heartPiece (tOp (C := C)) (op K) q).unop

/-- `coheartPiece K q` lies in degrees `≥ q`, since `heartPiece tOp (op K) q` lies in degrees
`≤ -q` for `tOp`. -/
instance coheartPiece_isGE (K : DerivedCategory C) (q : ℤ) : (coheartPiece K q).IsGE q := by
  have h := (opTStructure_isLE_iff (TStructure.t : TStructure (DerivedCategory C))
    (heartPiece (tOp (C := C)) (op K) q) (-q)).1 inferInstance
  simpa using h

/-- `coheartPiece K q` lies in degrees `≤ q`, since `heartPiece tOp (op K) q` lies in degrees
`≥ -q` for `tOp`. -/
instance coheartPiece_isLE (K : DerivedCategory C) (q : ℤ) : (coheartPiece K q).IsLE q := by
  have h := (opTStructure_isGE_iff (TStructure.t : TStructure (DerivedCategory C))
    (heartPiece (tOp (C := C)) (op K) q) (-q)).1 inferInstance
  simpa using h

/-- The triangle `(upperPiece tOp (op K) q).unop ⟶ K ⟶ Z ⟶ …` of `D(C)` obtained from the
triangle `upperTriangle tOp (op K) q` of `D(C)ᵒᵖ` by the inverse of `triangleOpEquivalence`. Its
first morphism is `(toUpperPiece tOp (op K) q).unop` and its third object `Z` lies in degrees
`≥ q + 1`. Classically it is `τ_{≤ q} K ⟶ K ⟶ τ_{≥ q + 1} K ⟶ …`. -/
def coupperTriangle (K : DerivedCategory C) (q : ℤ) : Triangle (DerivedCategory C) :=
  ((triangleOpEquivalence (DerivedCategory C)).inverse.obj
    (upperTriangle (tOp (C := C)) (op K) q)).unop

lemma coupperTriangle_distinguished (K : DerivedCategory C) (q : ℤ) :
    coupperTriangle K q ∈ distTriang (DerivedCategory C) :=
  unop_distinguished _ (upperTriangle_distinguished _ _ _)

lemma coupperTriangle_mor₁ (K : DerivedCategory C) (q : ℤ) :
    (coupperTriangle K q).mor₁ = (toUpperPiece (tOp (C := C)) (op K) q).unop := rfl

instance coupperTriangle_obj₃_isGE (K : DerivedCategory C) (q : ℤ) :
    (coupperTriangle K q).obj₃.IsGE (q + 1) := by
  have h := (opTStructure_isLE_iff (TStructure.t : TStructure (DerivedCategory C))
    (upperTriangle (tOp (C := C)) (op K) q).obj₁ (-(q + 1))).1 inferInstance
  rw [neg_neg] at h
  exact h

/-- The triangle `Z ⟶ (upperPiece tOp (op K) q).unop ⟶ coheartPiece K q ⟶ …` of `D(C)` obtained
from the triangle `heartTriangle tOp (op K) q` of `D(C)ᵒᵖ` by the inverse of
`triangleOpEquivalence`. Its second morphism is `(heartPieceToUpperPiece tOp (op K) q).unop` and
its first object `Z` lies in degrees `≤ q - 1`. Classically it is
`τ_{≤ q - 1} K ⟶ τ_{≤ q} K ⟶ τ_{≥ q} τ_{≤ q} K ⟶ …`. -/
def coheartTriangle (K : DerivedCategory C) (q : ℤ) : Triangle (DerivedCategory C) :=
  ((triangleOpEquivalence (DerivedCategory C)).inverse.obj
    (heartTriangle (tOp (C := C)) (op K) q)).unop

lemma coheartTriangle_distinguished (K : DerivedCategory C) (q : ℤ) :
    coheartTriangle K q ∈ distTriang (DerivedCategory C) :=
  unop_distinguished _ (heartTriangle_distinguished _ _ _)

lemma coheartTriangle_mor₂ (K : DerivedCategory C) (q : ℤ) :
    (coheartTriangle K q).mor₂ = (heartPieceToUpperPiece (tOp (C := C)) (op K) q).unop := rfl

instance coheartTriangle_obj₁_isLE (K : DerivedCategory C) (q : ℤ) :
    (coheartTriangle K q).obj₁.IsLE (q - 1) := by
  have h := (opTStructure_isGE_iff (TStructure.t : TStructure (DerivedCategory C))
    (heartTriangle (tOp (C := C)) (op K) q).obj₃ (-(q - 1))).1 inferInstance
  rw [neg_neg] at h
  exact h

/-- `H^q` of the first morphism of `coupperTriangle K q` is an isomorphism: the third object has
zero cohomology in degrees `q - 1` and `q`. -/
instance isIso_homologyMap_coupperTriangle_mor₁ (K : DerivedCategory C) (q : ℤ) :
    IsIso ((homologyFunctor C q).map (coupperTriangle K q).mor₁) := by
  have hT := coupperTriangle_distinguished K q
  have hZ : IsZero ((homologyFunctor C q).obj (coupperTriangle K q).obj₃) :=
    isZero_of_isGE _ (q + 1) q (by lia)
  have hZ' : IsZero ((homologyFunctor C (q - 1)).obj (coupperTriangle K q).obj₃) :=
    isZero_of_isGE _ (q + 1) (q - 1) (by lia)
  have hm : Mono ((homologyFunctor C q).map (coupperTriangle K q).mor₁) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₁_iff _ hT (q - 1) q
      (by lia)).2 (hZ'.eq_of_src _ _)
  have he : Epi ((homologyFunctor C q).map (coupperTriangle K q).mor₁) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₁_iff _ hT q).2
      (hZ.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- `H^q` of the second morphism of `coheartTriangle K q` is an isomorphism: the first object
has zero cohomology in degrees `q` and `q + 1`. -/
instance isIso_homologyMap_coheartTriangle_mor₂ (K : DerivedCategory C) (q : ℤ) :
    IsIso ((homologyFunctor C q).map (coheartTriangle K q).mor₂) := by
  have hT := coheartTriangle_distinguished K q
  have hZ : IsZero ((homologyFunctor C q).obj (coheartTriangle K q).obj₁) :=
    isZero_of_isLE _ (q - 1) q (by lia)
  have hZ' : IsZero ((homologyFunctor C (q + 1)).obj (coheartTriangle K q).obj₁) :=
    isZero_of_isLE _ (q - 1) (q + 1) (by lia)
  have hm : Mono ((homologyFunctor C q).map (coheartTriangle K q).mor₂) :=
    ((homologyFunctor C 0).homologySequence_mono_shift_map_mor₂_iff _ hT q).2
      (hZ.eq_of_src _ _)
  have he : Epi ((homologyFunctor C q).map (coheartTriangle K q).mor₂) :=
    ((homologyFunctor C 0).homologySequence_epi_shift_map_mor₂_iff _ hT q (q + 1) rfl).2
      (hZ'.eq_of_tgt _ _)
  exact @isIso_of_mono_of_epi _ _ _ _ _ _ hm he

/-- The comparison isomorphism `H^q(coheartPiece K q) ≅ H^q(K)`: the inverse of the isomorphism
induced by `(heartPieceToUpperPiece tOp (op K) q).unop`, followed by the isomorphism induced by
`(toUpperPiece tOp (op K) q).unop`. -/
def coheartPieceHomologyIso (K : DerivedCategory C) (q : ℤ) :
    (homologyFunctor C q).obj (coheartPiece K q) ≅ (homologyFunctor C q).obj K :=
  (@asIso _ _ _ _ ((homologyFunctor C q).map (coheartTriangle K q).mor₂)
      (isIso_homologyMap_coheartTriangle_mor₂ K q)).symm ≪≫
    @asIso _ _ _ _ ((homologyFunctor C q).map (coupperTriangle K q).mor₁)
      (isIso_homologyMap_coupperTriangle_mor₁ K q)

/-- `coheartPiece K q`, the object of `D(C)` underlying `heartPiece tOp (op K) q`, is isomorphic
to `H^q(K)` placed in degree `q`. -/
def coheartPieceIso (K : DerivedCategory C) (q : ℤ) :
    coheartPiece K q ≅ (singleFunctor C q).obj ((homologyFunctor C q).obj K) :=
  isoSingleHomology _ q ≪≫ (singleFunctor C q).mapIso (coheartPieceHomologyIso K q)

/-- The additive equivalence `Hom(heartPiece tOp (op K) q, (op A₀)⟦p + q⟧) ≃+ Ext^p(A, H^q(K))`
for `p : ℕ`, where `A₀` is `A` placed in degree `0`. Writing `M = H^q(K)` and `M₀` for `M` placed
in degree `0`, it identifies `(op A₀)⟦p + q⟧` with `op (A₀⟦-(p + q)⟧)`, passes to `D(C)`,
postcomposes with `coheartPieceIso K q` and with `(singleFunctor C q).obj M ≅ M₀⟦-q⟧`, shifts by
`p + q`, identifies `A₀⟦-(p + q)⟧⟦p + q⟧` with `A₀` and `M₀⟦-q⟧⟦p + q⟧` with `M₀⟦p⟧`, and applies
the inverse of `Abelian.Ext.homAddEquiv`. -/
def secondPageAddEquiv [HasExt.{w'} C] (K : DerivedCategory C) (A : C) (p : ℕ) (q : ℤ) :
    (heartPiece (tOp (C := C)) (op K) q ⟶ (op ((singleFunctor C 0).obj A))⟦(p : ℤ) + q⟧) ≃+
      Abelian.Ext.{w'} A ((homologyFunctor C q).obj K) p :=
  (postcompAddEquiv _ ((shiftFunctorOpIso (DerivedCategory C) ((p : ℤ) + q) (-((p : ℤ) + q))
      (by lia)).app (op ((singleFunctor C 0).obj A)))).trans <|
    (unopAddEquiv _ _).trans <|
    (postcompAddEquiv _ (coheartPieceIso K q)).trans <|
    (postcompAddEquiv _ (((singleFunctors C).shiftIso (-q) q 0 (by lia)).app
      ((homologyFunctor C q).obj K)).symm).trans <|
    (shiftAddEquiv _ _ ((p : ℤ) + q)).trans <|
    (precompAddEquiv ((shiftFunctorCompIsoId (DerivedCategory C) (-((p : ℤ) + q)) ((p : ℤ) + q)
      (by lia)).app ((singleFunctor C 0).obj A)).symm _).trans <|
    (postcompAddEquiv _ ((shiftFunctorAdd' (DerivedCategory C) (-q) ((p : ℤ) + q) (p : ℤ)
      (by lia)).app ((singleFunctor C 0).obj ((homologyFunctor C q).obj K))).symm).trans
    Abelian.Ext.homAddEquiv.symm

/-- The abutment in total degree `n`: `(op K ⟶ (op A₀)⟦n⟧) ≃+ ShiftedHom A₀ K n`. It identifies
`(op A₀)⟦n⟧` with `op (A₀⟦-n⟧)`, passes to `D(C)`, shifts by `n` and identifies `A₀⟦-n⟧⟦n⟧`
with `A₀`. -/
def abutmentAddEquiv (K : DerivedCategory C) (A : C) (n : ℤ) :
    (op K ⟶ (op ((singleFunctor C 0).obj A))⟦n⟧) ≃+
      ShiftedHom ((singleFunctor C 0).obj A) K n :=
  (postcompAddEquiv _ ((shiftFunctorOpIso (DerivedCategory C) n (-n) (by lia)).app
      (op ((singleFunctor C 0).obj A)))).trans <|
    (unopAddEquiv _ _).trans <|
    (shiftAddEquiv _ _ n).trans <|
    precompAddEquiv ((shiftFunctorCompIsoId (DerivedCategory C) (-n) n (by lia)).app
      ((singleFunctor C 0).obj A)).symm _

/-- The objects in positions `(p, q)` with `p < 0` on page 2 of the covariant hyperext spectral
sequence are zero: `heartPiece tOp (op K) q` lies in degrees `≤ -q` and `(op A₀)⟦p + q⟧` in
degrees `≥ -(p + q)` for `tOp`, and `-q < -(p + q)`. -/
lemma isZero_secondPage_of_neg (K : DerivedCategory C) (A : C) (p q : ℤ) (hp : p < 0) :
    IsZero (((hyperextSpectralSequence (tOp (C := C)) (op K)
      (op ((singleFunctor C 0).obj A))).page 2).X ⟨p, q⟩) := by
  refine IsZero.of_iso ?_
    (secondPageIso (tOp (C := C)) (op K) (op ((singleFunctor C 0).obj A)) p q)
  have h0 : (tOp (C := C)).IsGE (op ((singleFunctor C 0).obj A)) 0 :=
    (opTStructure_isGE_iff _ _ 0).2 (by simpa using
      (inferInstance : ((singleFunctor C 0).obj A).IsLE 0))
  have : (tOp (C := C)).IsGE ((op ((singleFunctor C 0).obj A))⟦p + q⟧) (-(p + q)) :=
    (tOp (C := C)).isGE_shift _ 0 (p + q) (-(p + q)) (by lia)
  have : Subsingleton (heartPiece (tOp (C := C)) (op K) q ⟶
      (op ((singleFunctor C 0).obj A))⟦p + q⟧) :=
    ⟨fun f g => ((tOp (C := C)).zero_of_isLE_of_isGE f (-q) (-(p + q)) (by lia) inferInstance
      this).trans ((tOp (C := C)).zero_of_isLE_of_isGE g (-q) (-(p + q)) (by lia) inferInstance
        this).symm⟩
  exact AddCommGrpCat.isZero_of_iff_subsingleton.2 this

end Derived

end CovariantSecondPage

universe w w' v u

open CovariantSecondPage HyperextSpectralSequence in
/-- Proof of `CovariantSecondPageStatement`: the page-2 objects in positions `(p, q)`, `p : ℕ`,
are `Ext^p(A, H^q(K))` by `secondPageIso` and `secondPageAddEquiv`; those with `p < 0` vanish by
`isZero_secondPage_of_neg`; the abutment is `ShiftedHom A₀ K n` by `abutmentAddEquiv`. -/
theorem covariantSecondPageStatement_proof (C : Type u) [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] : CovariantSecondPageStatement.{w, w', v, u} C := by
  intro _ K A
  refine ⟨fun p q => ⟨?_⟩, fun p q hp => isZero_secondPage_of_neg K A p q hp,
    fun n => ⟨abutmentAddEquiv K A n⟩⟩
  exact (secondPageIso _ (op K) (op ((DerivedCategory.singleFunctor C 0).obj A)) p q
    ).addCommGroupIsoToAddEquiv.trans (secondPageAddEquiv K A p q)

end HyperextConvergence

end Langlands.Cohomology
