import Langlands.GroupScheme.Rational.VectorActionCharZero
import Langlands.GroupScheme.Rational.SplitUnipotentTransport
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Products
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Combining linear vector coordinates and the characteristic-zero case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Concatenate two additive coordinate tuples, including empty tuples. -/
def vectorTupleProductEquiv (R : Type u) [AddGroup R] (n m : ℕ) :
    Multiplicative (Fin n → R) × Multiplicative (Fin m → R) ≃*
      Multiplicative (Fin (n + m) → R) where
  toFun x := Multiplicative.ofAdd (Fin.append x.1.toAdd x.2.toAdd)
  invFun x := (Multiplicative.ofAdd fun i => x.toAdd (Fin.castAdd m i),
    Multiplicative.ofAdd fun i => x.toAdd (Fin.natAdd n i))
  left_inv x := by
    apply Prod.ext <;> apply Multiplicative.toAdd.injective <;> funext i <;> simp
  right_inv x := by
    apply Multiplicative.toAdd.injective
    exact Fin.append_castAdd_natAdd
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    induction i using Fin.addCases <;> simp

variable {k : Type u} [Field k]
    {H V F M : GroupScheme (Spec (CommRingCat.of k))} {n m : ℕ}
    (eF : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ F.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (eM : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ M.X) ≃* Multiplicative (Fin m → Γ(T.left, ⊤)))

/-- Concatenate natural vector coordinates on an actual product of groups. -/
def vectorProductCoordinates (T : Over (Spec (CommRingCat.of k))) :
    (T ⟶ (F ⊗ M).X) ≃* Multiplicative (Fin (n + m) → Γ(T.left, ⊤)) :=
  (productPointsEquiv F M T).trans
    ((MulEquiv.prodCongr (eF T) (eM T)).trans
      (vectorTupleProductEquiv Γ(T.left, ⊤) n m))

@[simp] theorem vectorProductCoordinates_castAdd
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (F ⊗ M).X) (i : Fin n) :
    (vectorProductCoordinates eF eM T v).toAdd (Fin.castAdd m i) =
      (eF T (v ≫ fst F.X M.X)).toAdd i := by
  simp [vectorProductCoordinates, vectorTupleProductEquiv]
  rfl

@[simp] theorem vectorProductCoordinates_natAdd
    (T : Over (Spec (CommRingCat.of k))) (v : T ⟶ (F ⊗ M).X) (i : Fin m) :
    (vectorProductCoordinates eF eM T v).toAdd (Fin.natAdd n i) =
      (eM T (v ≫ snd F.X M.X)).toAdd i := by
  simp [vectorProductCoordinates, vectorTupleProductEquiv]
  rfl

variable {eF eM}

/-- Naturality of both factors gives naturality on every product test. -/
theorem IsNaturalVectorCoordinates.prod
    (hF : IsNaturalVectorCoordinates eF) (hM : IsNaturalVectorCoordinates eM) :
    IsNaturalVectorCoordinates (vectorProductCoordinates eF eM) := by
  intro T W f v
  funext i
  induction i using Fin.addCases with
  | left i =>
    simpa only [vectorProductCoordinates_castAdd, Category.assoc] using
      congrFun (hF T W f (v ≫ fst F.X M.X)) i
  | right i =>
    simpa only [vectorProductCoordinates_natAdd, Category.assoc] using
      congrFun (hM T W f (v ≫ snd F.X M.X)) i

/-- Scalar multiplication in concatenated coordinates restricts to scalar
multiplication in the first factor. -/
theorem vectorProductCoordinates_smul_fst
    (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (v : T ⟶ (F ⊗ M).X) :
    (vectorProductCoordinates eF eM T).symm
        (Multiplicative.ofAdd (c • (vectorProductCoordinates eF eM T v).toAdd)) ≫
        fst F.X M.X =
      (eF T).symm (Multiplicative.ofAdd
        (c • (eF T (v ≫ fst F.X M.X)).toAdd)) := by
  apply (eF T).injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply]
  funext i
  have h := congrArg (fun z => z.toAdd (Fin.castAdd m i))
    ((vectorProductCoordinates eF eM T).apply_symm_apply
      (Multiplicative.ofAdd (c • (vectorProductCoordinates eF eM T v).toAdd)))
  simpa only [vectorProductCoordinates_castAdd, toAdd_ofAdd, Pi.smul_apply] using h

/-- Scalar multiplication in concatenated coordinates restricts to scalar
multiplication in the second factor. -/
theorem vectorProductCoordinates_smul_snd
    (T : Over (Spec (CommRingCat.of k))) (c : Γ(T.left, ⊤))
    (v : T ⟶ (F ⊗ M).X) :
    (vectorProductCoordinates eF eM T).symm
        (Multiplicative.ofAdd (c • (vectorProductCoordinates eF eM T v).toAdd)) ≫
        snd F.X M.X =
      (eM T).symm (Multiplicative.ofAdd
        (c • (eM T (v ≫ snd F.X M.X)).toAdd)) := by
  apply (eM T).injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply]
  funext i
  have h := congrArg (fun z => z.toAdd (Fin.natAdd n i))
    ((vectorProductCoordinates eF eM T).apply_symm_apply
      (Multiplicative.ofAdd (c • (vectorProductCoordinates eF eM T v).toAdd)))
  simpa only [vectorProductCoordinates_natAdd, toAdd_ofAdd, Pi.smul_apply] using h

/-- An actual action on a product is linear in concatenated coordinates when
both projections intertwine actions linear in the factor coordinates. -/
theorem IsLinearVectorCoordinates.prod
    {bF : AutomorphicAction H F} {bM : AutomorphicAction H M}
    (hF : IsLinearVectorCoordinates bF eF) (hM : IsLinearVectorCoordinates bM eM)
    (b : AutomorphicAction H (F ⊗ M))
    (hfst : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ (F ⊗ M).X),
      b.act h v ≫ fst F.X M.X = bF.act h (v ≫ fst F.X M.X))
    (hsnd : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ (F ⊗ M).X),
      b.act h v ≫ snd F.X M.X = bM.act h (v ≫ snd F.X M.X)) :
    IsLinearVectorCoordinates b (vectorProductCoordinates eF eM) := by
  refine ⟨hF.1.prod hM.1, ?_⟩
  intro T h c v
  funext i
  induction i using Fin.addCases with
  | left i =>
    simp only [vectorProductCoordinates_castAdd, Pi.smul_apply, hfst,
      vectorProductCoordinates_smul_fst]
    exact congrFun (hF.2 T h c (v ≫ fst F.X M.X)) i
  | right i =>
    simp only [vectorProductCoordinates_natAdd, Pi.smul_apply, hsnd,
      vectorProductCoordinates_smul_snd]
    exact congrFun (hM.2 T h c (v ≫ snd F.X M.X)) i

/-- A pointwise trivial action is linear in any natural vector coordinates. -/
theorem IsNaturalVectorCoordinates.isLinear_of_act_eq
    (hF : IsNaturalVectorCoordinates eF) (bF : AutomorphicAction H F)
    (hact : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ F.X), bF.act h v = v) :
    IsLinearVectorCoordinates bF eF := by
  refine ⟨hF, ?_⟩
  intro T h c v
  simp only [hact, MulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- Natural coordinates transport through an actual group-scheme isomorphism. -/
theorem IsNaturalVectorCoordinates.of_iso
    (hF : IsNaturalVectorCoordinates eF) (f : F ≅ V) :
    IsNaturalVectorCoordinates (vectorCoordinatesOfIso f eF) := by
  intro T W g v
  simpa only [vectorCoordinatesOfIso_apply, Category.assoc] using
    hF T W g (v ≫ f.inv.hom.hom)

/-- Linear coordinates transport through an equivariant group-scheme isomorphism. -/
theorem IsLinearVectorCoordinates.of_iso
    {bF : AutomorphicAction H F} (hF : IsLinearVectorCoordinates bF eF)
    (f : F ≅ V) (b : AutomorphicAction H V)
    (hf : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X)
      (v : T ⟶ V.X), b.act h v ≫ f.inv.hom.hom =
        bF.act h (v ≫ f.inv.hom.hom)) :
    IsLinearVectorCoordinates b (vectorCoordinatesOfIso f eF) := by
  refine ⟨hF.1.of_iso f, ?_⟩
  intro T h c v
  have hsmul :
      (vectorCoordinatesOfIso f eF T).symm
          (Multiplicative.ofAdd (c • (vectorCoordinatesOfIso f eF T v).toAdd)) ≫
          f.inv.hom.hom =
        (eF T).symm (Multiplicative.ofAdd
          (c • (eF T (v ≫ f.inv.hom.hom)).toAdd)) := by
    apply (eF T).injective
    rw [MulEquiv.apply_symm_apply]
    change (vectorCoordinatesOfIso f eF T)
      ((vectorCoordinatesOfIso f eF T).symm _) = _
    exact (vectorCoordinatesOfIso f eF T).apply_symm_apply _
  change (eF T (b.act h ((vectorCoordinatesOfIso f eF T).symm
    (Multiplicative.ofAdd (c • (vectorCoordinatesOfIso f eF T v).toAdd))) ≫
    f.inv.hom.hom)).toAdd =
      c • (eF T (b.act h v ≫ f.inv.hom.hom)).toAdd
  rw [hf, hsmul, hf]
  exact hF.2 T h c (v ≫ f.inv.hom.hom)

/-- Every naturally coordinatized vector group admits linear coordinates for
an affine acting group in characteristic zero. -/
theorem IsVectorGroup.exists_linearCoordinates_of_charZero [CharZero k]
    [IsAffineHom H.X.hom] (hV : IsVectorGroup V) (b : AutomorphicAction H V) :
    ∃ (d : ℕ) (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))),
      IsLinearVectorCoordinates b e := by
  obtain ⟨d, e, he⟩ := hV
  exact ⟨d, e, isLinearVectorCoordinates_of_charZero (b := b) he⟩

/-- The split-torus existence case in characteristic zero, over any field. -/
theorem IsVectorGroup.exists_splitTorusLinearCoordinates_of_charZero [CharZero k]
    (hV : IsVectorGroup V) (S : CommGroupScheme (Spec (CommRingCat.of k)))
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp V) :
    ∃ (d : ℕ) (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤))),
      IsLinearVectorCoordinates b e := by
  let := hS.isAffineHom
  exact hV.exists_linearCoordinates_of_charZero b

end Langlands.GroupScheme.RelativeRoot
