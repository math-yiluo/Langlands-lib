import Langlands.GroupScheme.Quaternionic.BinaryQuaternionSpinLift
import Langlands.GroupScheme.CentralIsogeny.CommutingLifts

/-! # The combined binary quaternionic homomorphism into a supplied spin cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] {σ : FirstKindInvolution K D}
  {n : Type} [Fintype n] [DecidableEq n] {q : σ.QuadraticForms n}
  {S C E : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}

/-- Commutation of two connected reductive images can be checked in the supplied
isometry group. -/
theorem commute_of_comp (hπ : σ.IsSpinCover q π)
    (a : C ⟶ S) (b : E ⟶ S)
    (hC : IsConnectedReductive C) (hE : IsConnectedReductive E)
    (hc : ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ C.X) (y : T ⟶ E.X),
      Commute (x ≫ (a ≫ π).hom.hom) (y ≫ (b ≫ π).hom.hom)) :
    ∀ (T : Over (Spec (CommRingCat.of K))) (x : T ⟶ C.X) (y : T ⟶ E.X),
      Commute (x ≫ a.hom.hom) (y ≫ b.hom.hom) := by
  let := hπ.smooth
  obtain ⟨p, hp, hpp⟩ := hπ.exists_centralIsogeny
  let := hp.kernel_isFinite
  apply commute_of_finiteKernel p a b hC hE
  intro T x y
  apply (commute_iff_eq _ _).2
  apply (cancel_mono (identityComponentι (σ.isometryGroup q)).hom.hom).mp
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simpa only [Category.assoc, ← Grp.comp_hom_hom, hpp] using (hc T x y).eq

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.IsSpinCover

namespace Langlands.GroupScheme.Quaternionic.BinarySpinLift

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

/-- The two binary factor inclusions commute on every relative test scheme. -/
theorem first_second_commute (T : Over (Spec (CommRingCat.of K)))
    (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X)
    (y : T ⟶ (CentralSimpleUnits.normOne K D).X) :
    Commute (x ≫ (firstFactor (K := K) (D := D)).hom.hom)
      (y ≫ (secondFactor (K := K) (D := D)).hom.hom) := by
  apply (commute_iff_eq _ _).2
  apply (BinaryScheme.pointsEquiv T).injective
  rw [map_mul, map_mul, firstFactor_points, secondFactor_points]
  apply Prod.ext <;> simp only [Prod.fst_mul, Prod.snd_mul, mul_one, one_mul]

/-- Every point of the binary product decomposes into its two factor inclusions. -/
theorem factor_decomposition (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    ((z ≫ fst _ _) ≫ firstFactor.hom.hom) *
      ((z ≫ snd _ _) ≫ secondFactor.hom.hom) = z := by
  apply (BinaryScheme.pointsEquiv T).injective
  rw [map_mul, firstFactor_points, secondFactor_points]
  apply Prod.ext
  · simp only [Prod.fst_mul, mul_one]
    rfl
  · simp only [Prod.snd_mul, one_mul]
    rfl

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {e f : n → D} (h : σ.IsHyperbolicPair q e f)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- The separate lifts of SL₂ and the norm-one group commute on every test. -/
theorem specialLinear_normOne_commute :
    ∀ (T : Over (Spec (CommRingCat.of K)))
      (x : T ⟶ (SpecialLinear.groupScheme (Fin 2) (CommRingCat.of K)).X)
      (y : T ⟶ (CentralSimpleUnits.normOne K D).X),
      Commute (x ≫ (specialLinear σ hdim hsym h hπ hsc).hom.hom)
        (y ≫ (normOne σ hdim hsym h hπ hsc).hom.hom) := by
  apply hπ.commute_of_comp _ _
    (specialLinear_simplyConnected hsc K).isSemisimple.isConnectedReductive
    (hsc K D hdim).isSemisimple.isConnectedReductive
  intro T x y
  rw [specialLinear_comp, normOne_comp]
  have hc := first_second_commute (D := D) T x y
  exact hc.map ((pointsMap (AmbientBinaryScheme.isometryHom σ hdim hsym h)).app
    (Opposite.op T)).hom

/-- The actual combined binary homomorphism into the given spin group. -/
def productHom : BinaryScheme.groupScheme (K := K) (D := D) ⟶ S :=
  commutingSubgroupMultiplicationHom
    (specialLinear σ hdim hsym h hπ hsc) (normOne σ hdim hsym h hπ hsc)
    (specialLinear_normOne_commute σ hdim hsym h hπ hsc)

/-- The combined homomorphism is the product of the two lifted coordinate points. -/
theorem productHom_points (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    z ≫ (productHom σ hdim hsym h hπ hsc).hom.hom =
      ((z ≫ fst _ _) ≫ (specialLinear σ hdim hsym h hπ hsc).hom.hom) *
        ((z ≫ snd _ _) ≫ (normOne σ hdim hsym h hπ hsc).hom.hom) := by
  change z ≫ subgroupMultiplication _ _ = _
  simp only [subgroupMultiplication, MonObj.comp_mul, Category.assoc]

/-- The full combined spin action has exactly the original ambient product action. -/
@[reassoc] theorem productHom_comp :
    productHom σ hdim hsym h hπ hsc ≫ π =
      AmbientBinaryScheme.isometryHom σ hdim hsym h := by
  apply Grp.hom_ext
  change subgroupMultiplication _ _ ≫ π.hom.hom = _
  have ha : (specialLinear σ hdim hsym h hπ hsc).hom.hom ≫ π.hom.hom =
      firstFactor.hom.hom ≫ (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom := by
    rw [← Grp.comp_hom_hom, specialLinear_comp, Grp.comp_hom_hom]
  have hb : (normOne σ hdim hsym h hπ hsc).hom.hom ≫ π.hom.hom =
      secondFactor.hom.hom ≫ (AmbientBinaryScheme.isometryHom σ hdim hsym h).hom.hom := by
    rw [← Grp.comp_hom_hom, normOne_comp, Grp.comp_hom_hom]
  have hd := factor_decomposition (K := K) (D := D)
    (BinaryScheme.groupScheme (K := K) (D := D)).X (𝟙 _)
  simp only [Category.id_comp] at hd
  rw [subgroupMultiplication, MonObj.mul_comp]
  simp only [Category.assoc, ha, hb]
  rw [← Category.assoc, ← Category.assoc, ← MonObj.mul_comp]
  rw [hd]
  exact Category.id_comp _

/-- All relative test points of the combined lift have the prescribed ambient matrix. -/
theorem productHom_ambient_points (T : Over (Spec (CommRingCat.of K)))
    (z : T ⟶ (BinaryScheme.groupScheme (K := K) (D := D)).X) :
    HyperbolicScheme.matrixPointsEquiv n T
      (((z ≫ (productHom σ hdim hsym h hπ hsc).hom.hom) ≫ π.hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (BinaryScheme.coefficients T)
        (BinaryScheme.pointMatrix σ hdim hsym T z) := by
  rw [Category.assoc z, ← Grp.comp_hom_hom, productHom_comp]
  exact AmbientBinaryScheme.isometryHom_points σ hdim hsym h T z

end Langlands.GroupScheme.Quaternionic.BinarySpinLift
