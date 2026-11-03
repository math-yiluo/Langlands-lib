import Langlands.GroupScheme.Dynamic.AdjointDeterminantModelIndependenceStatement
import Langlands.GroupScheme.Lie.KernelTargetMaps

/-! # Proof of model and coordinate independence of the adjoint determinant character -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}}

/-- Rational characters of an affine group scheme over `Spec R` are determined by their values
on points over `R`-algebras. -/
theorem rationalCharacters_ext_affinePoints {H : GroupScheme (Spec R)} [IsAffine H.X.left]
    {χ ψ : rationalCharacters H}
    (h : ∀ (A : CommAlgCat.{u} R) (p : H.affinePoints A),
      p ≫ χ.toMul.hom.hom = p ≫ ψ.toMul.hom.hom) :
    χ = ψ := by
  apply congrArg Additive.ofMul
  apply hom_ext_points
  intro T x
  obtain ⟨⟨B⟩, ⟨e⟩⟩ := (essImage_algSpec (G := H.X)).mpr inferInstance
  have hB : e.hom ≫ χ.toMul.hom.hom = e.hom ≫ ψ.toMul.hom.hom := h B e.hom
  have hx : x = (x ≫ e.inv) ≫ e.hom := by simp
  rw [hx, Category.assoc, Category.assoc]
  exact congrArg (fun f => (x ≫ e.inv) ≫ f) hB

/-- An isomorphism of group schemes induces a linear isomorphism of the actual Lie kernels. -/
def lieKernelLinearEquiv {U U' : GroupScheme (Spec R)} [IsAffineHom U.X.hom]
    [IsAffineHom U'.X.hom] (e : U ≅ U') (A : Type u) [CommRing A] [Algebra R A] :
    Additive (lieKernel U A) ≃ₗ[A] Additive (lieKernel U' A) where
  toLinearMap := Lie.targetMapLinear e.hom A
  invFun := Lie.targetMapLinear e.inv A
  left_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x.toMul.val ≫ e.hom.hom.hom) ≫ e.inv.hom.hom = x.toMul.val
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  right_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (x.toMul.val ≫ e.inv.hom.hom) ≫ e.hom.hom.hom = x.toMul.val
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]

@[simp] theorem lieKernelLinearEquiv_val {U U' : GroupScheme (Spec R)} [IsAffineHom U.X.hom]
    [IsAffineHom U'.X.hom] (e : U ≅ U') {A : Type u} [CommRing A] [Algebra R A]
    (x : Additive (lieKernel U A)) :
    (lieKernelLinearEquiv e A x).toMul.val = x.toMul.val ≫ e.hom.hom.hom := rfl

@[simp] theorem lieKernelLinearEquiv_symm_val {U U' : GroupScheme (Spec R)}
    [IsAffineHom U.X.hom] [IsAffineHom U'.X.hom] (e : U ≅ U') {A : Type u} [CommRing A]
    [Algebra R A] (x : Additive (lieKernel U' A)) :
    ((lieKernelLinearEquiv e A).symm x).toMul.val = x.toMul.val ≫ e.inv.hom.hom := rfl

namespace AutomorphicAction

variable {H H' U U' : GroupScheme (Spec R)} [IsAffineHom U.X.hom] [IsAffineHom U'.X.hom]
  (a : AutomorphicAction H U) (a' : AutomorphicAction H' U') (φ : H ⟶ H') (e : U ≅ U')

/-- If `φ` and `e` intertwine the two actions on all test points, then the differential of
`a'` at the image of `h` is the conjugate of the differential of `a` at `h` by the induced Lie
kernel isomorphism. -/
theorem differential_comp_eq_conj
    (he : ∀ {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ U.X),
      a'.act (h ≫ φ.hom.hom) (x ≫ e.hom.hom.hom) = a.act h x ≫ e.hom.hom.hom)
    {A : Type u} [CommRing A] [Algebra R A] (h : Lie.AffinePoints H A) :
    a'.differential (h ≫ φ.hom.hom) =
      ((lieKernelLinearEquiv e A).symm.trans (a.differential h)).trans
        (lieKernelLinearEquiv e A) := by
  apply LinearEquiv.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  change a'.act (Lie.constant H' (h ≫ φ.hom.hom)) x.toMul.val =
    a.act (Lie.constant H h) (x.toMul.val ≫ e.inv.hom.hom) ≫ e.hom.hom.hom
  have hc : Lie.constant H' (h ≫ φ.hom.hom) = Lie.constant H h ≫ φ.hom.hom := by
    simp only [Lie.constant, Lie.affineMap_apply, Category.assoc]
  have hx : x.toMul.val = (x.toMul.val ≫ e.inv.hom.hom) ≫ e.hom.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]
  rw [hc, hx, he, ← hx]

/-- Under the same intertwining hypothesis the two differentials have the same determinant. -/
theorem det_differential_comp
    (he : ∀ {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ U.X),
      a'.act (h ≫ φ.hom.hom) (x ≫ e.hom.hom.hom) = a.act h x ≫ e.hom.hom.hom)
    {A : Type u} [CommRing A] [Algebra R A] (h : Lie.AffinePoints H A) :
    LinearEquiv.det (a'.differential (h ≫ φ.hom.hom)) = LinearEquiv.det (a.differential h) := by
  rw [differential_comp_eq_conj a a' φ e he, LinearEquiv.det_conj]

/-- Under the same intertwining hypothesis the determinant character of `a'`, in any finite
coordinates, restricts along `φ` to the determinant character of `a`, in any finite
coordinates. -/
theorem characterRestrict_determinantCharacter_of_intertwining [IsAffine H.X.left] [IsAffine H'.X.left]
    (he : ∀ {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ U.X),
      a'.act (h ≫ φ.hom.hom) (x ≫ e.hom.hom.hom) = a.act h x ≫ e.hom.hom.hom)
    {d d' : ℕ} (c : Lie.FiniteCoordinates U d) (c' : Lie.FiniteCoordinates U' d') :
    characterRestrict φ (a'.determinantCharacter c') = a.determinantCharacter c := by
  apply rationalCharacters_ext_affinePoints
  intro A p
  have hp : p ≫ (characterRestrict φ (a'.determinantCharacter c')).toMul.hom.hom =
      (p ≫ φ.hom.hom) ≫ (a'.determinantCharacter c').toMul.hom.hom := by
    rw [characterRestrict_apply, Grp.comp_hom_hom, Category.assoc]
  rw [hp]
  apply (Gm.affinePointsEquiv ((algSpec R).obj (op A)).hom).injective
  exact (a'.determinantCharacter_affinePoints c' A (p ≫ φ.hom.hom)).trans
    ((det_differential_comp a a' φ e he p).trans (a.determinantCharacter_affinePoints c A p).symm)

omit [IsAffineHom U.X.hom] [IsAffineHom U'.X.hom] in
/-- Two conjugation actions computed after inclusions into a common ambient group are
intertwined by any compatible maps of the acting and acted-on group schemes. -/
theorem act_comp_of_conj {G : GroupScheme (Spec R)} {iH : H ⟶ G} {iH' : H' ⟶ G}
    {iU : U ⟶ G} {iU' : U' ⟶ G} [Mono iU'.hom.hom]
    (ha : ∀ {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ U.X),
      a.act h x ≫ iU.hom.hom = (h ≫ iH.hom.hom) * (x ≫ iU.hom.hom) * (h ≫ iH.hom.hom)⁻¹)
    (ha' : ∀ {T : Over (Spec R)} (h : T ⟶ H'.X) (x : T ⟶ U'.X),
      a'.act h x ≫ iU'.hom.hom =
        (h ≫ iH'.hom.hom) * (x ≫ iU'.hom.hom) * (h ≫ iH'.hom.hom)⁻¹)
    (hφ : φ ≫ iH' = iH) (heU : e.hom ≫ iU' = iU)
    {T : Over (Spec R)} (h : T ⟶ H.X) (x : T ⟶ U.X) :
    a'.act (h ≫ φ.hom.hom) (x ≫ e.hom.hom.hom) = a.act h x ≫ e.hom.hom.hom := by
  have hH : (h ≫ φ.hom.hom) ≫ iH'.hom.hom = h ≫ iH.hom.hom := by
    rw [Category.assoc, ← Grp.comp_hom_hom, hφ]
  have hU : ∀ y : T ⟶ U.X, (y ≫ e.hom.hom.hom) ≫ iU'.hom.hom = y ≫ iU.hom.hom := by
    intro y
    rw [Category.assoc, ← Grp.comp_hom_hom, heU]
  apply (cancel_mono iU'.hom.hom).1
  rw [ha', hH, hU, hU, ha]

end AutomorphicAction

namespace Dynamic

open SubgroupFunctor.IsRepresentedBy

/-- The adjoint determinant characters on the represented dynamic parabolic and centralizer are
independent of the represented models of `P(χ)`, `Z(χ)`, `U(χ)` and of the finite coordinates. -/
theorem adjointDeterminantModelIndependence :
    AdjointDeterminantModelIndependenceStatement.{u} := by
  intro R G χ U U' iU iU' hU hU' _ _ d d' c c'
  have : Mono iU'.hom.hom := hU'.1
  refine ⟨?_, ?_⟩
  · intro P P' iP iP' hP hP' _ _
    exact AutomorphicAction.characterRestrict_determinantCharacter_of_intertwining
      (parabolicAdjointAction hP hU) (parabolicAdjointAction hP' hU')
      (isoOfIsRepresentedBy hP hP').hom (isoOfIsRepresentedBy hU hU')
      (AutomorphicAction.act_comp_of_conj _ _ _ _
        (parabolicAdjointAction_act_comp hP hU) (parabolicAdjointAction_act_comp hP' hU')
        (isoOfIsRepresentedBy_hom_comp hP hP') (isoOfIsRepresentedBy_hom_comp hU hU'))
      c c'
  · intro Z Z' iZ iZ' hZ hZ' _ _
    exact AutomorphicAction.characterRestrict_determinantCharacter_of_intertwining
      (centralizerAdjointAction hZ hU) (centralizerAdjointAction hZ' hU')
      (isoOfIsRepresentedBy hZ hZ').hom (isoOfIsRepresentedBy hU hU')
      (AutomorphicAction.act_comp_of_conj _ _ _ _
        (centralizerAdjointAction_act_comp hZ hU) (centralizerAdjointAction_act_comp hZ' hU')
        (isoOfIsRepresentedBy_hom_comp hZ hZ') (isoOfIsRepresentedBy_hom_comp hU hU'))
      c c'

end Dynamic

end Langlands.GroupScheme
