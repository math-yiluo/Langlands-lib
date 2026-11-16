import Langlands.GroupScheme.AffineGmFixedScheme
import Langlands.GroupScheme.Dynamic.SmoothOverRing

/-! # Actual attracting schemes of affine multiplicative-group actions -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace PointwiseSchemeAction

variable {S : Scheme.{u}} {X : Over S} (s : PointwiseSchemeAction (Gm S).toGrp X)

/-- The actual orbit morphism of an arbitrary point under a multiplicative-group action. -/
def orbit {T : Over S} (x : T ⟶ X) : T ⊗ (Gm S).X ⟶ X :=
  s.act (snd _ _) (fst _ _ ≫ x)

/-- Restricting the test scheme restricts the orbit morphism. -/
theorem whiskerRight_orbit {T T' : Over S} (b : T' ⟶ T) (x : T ⟶ X) :
    b ▷ (Gm S).X ≫ s.orbit x = s.orbit (b ≫ x) := by
  simp only [orbit, s.naturality, whiskerRight_snd, whiskerRight_fst_assoc]

/-- An actual orbit extends along the standard inclusion of the multiplicative group. -/
def IsAttracted {T : Over S} (x : T ⟶ X) : Prop :=
  ∃ E : T ⊗ AffineLine.scheme S ⟶ X,
    T ◁ AffineLine.unitInclusion S ≫ E = s.orbit x

/-- Existence of an orbit extension is preserved by arbitrary scheme refinement. -/
theorem IsAttracted.comp {T T' : Over S} {x : T ⟶ X} (hx : s.IsAttracted x)
    (b : T' ⟶ T) : s.IsAttracted (b ≫ x) := by
  obtain ⟨E, hE⟩ := hx
  refine ⟨b ▷ AffineLine.scheme S ≫ E, ?_⟩
  rw [whisker_exchange_assoc, hE, s.whiskerRight_orbit]

end PointwiseSchemeAction

namespace GmCoordinateAction

open Langlands.CommutativeAlgebra.GradedFormallySmooth

variable {R : CommRingCat.{u}} {B C : CommAlgCat.{u} R}

/-- Polynomial functions on the affine line over an algebra. -/
abbrev polynomialAlgebra (C : CommAlgCat.{u} R) : CommAlgCat.{u} R :=
  CommAlgCat.of R (Polynomial C)

/-- The inclusion of polynomial functions into Laurent functions. -/
def polynomialInclusion (C : CommAlgCat.{u} R) :
    polynomialAlgebra C ⟶ laurentAlgebra C :=
  CommAlgCat.ofHom { Polynomial.toLaurent with
    commutes' := fun r => by
      change Polynomial.toLaurent (Polynomial.C (algebraMap R C r)) = _
      rw [Polynomial.toLaurent_C]
      rfl }

/-- Evaluation of a polynomial at a specified scalar. -/
def polynomialEvaluation (C : CommAlgCat.{u} R) (t : C) : polynomialAlgebra C ⟶ C :=
  CommAlgCat.ofHom ((Polynomial.aeval t : Polynomial C →ₐ[C] C).restrictScalars R)

/-- The explicit base map of an affine algebra spectrum. -/
abbrev affineTestMap (C : CommAlgCat.{u} R) : Spec (CommRingCat.of C) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R C))

/-- The polynomial spectrum comparison keeps the same underlying scheme. -/
def polynomialSchemeIso (C : CommAlgCat.{u} R) :
    (algSpec R).obj (op (polynomialAlgebra C)) ≅
      AffineLine.polynomialScheme (affineTestMap C) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of (Polynomial C)))) (by
    change 𝟙 _ ≫ Spec.map (AffineLine.polynomialC (CommRingCat.of C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Polynomial C)))
    rw [Category.id_comp, ← Spec.map_comp]
    exact congrArg (fun q : R ⟶ CommRingCat.of (Polynomial C) => Spec.map q)
      (CommRingCat.hom_ext (RingHom.ext fun r => rfl)))

/-- The Laurent spectrum comparison keeps the same underlying scheme. -/
def laurentSchemeIso (C : CommAlgCat.{u} R) :
    (algSpec R).obj (op (laurentAlgebra C)) ≅
      AffineLine.laurentScheme (affineTestMap C) :=
  Over.isoMk (Iso.refl (Spec (CommRingCat.of (LaurentPolynomial C)))) (by
    change 𝟙 _ ≫ Spec.map (AffineLine.polynomialToLaurent (CommRingCat.of C)) ≫
        Spec.map (AffineLine.polynomialC (CommRingCat.of C)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R C)) =
      Spec.map (CommRingCat.ofHom (algebraMap R (LaurentPolynomial C)))
    rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change Polynomial.toLaurent (Polynomial.C (algebraMap R C r)) =
      algebraMap R (LaurentPolynomial C) r
    rw [Polynomial.toLaurent_C, LaurentPolynomial.algebraMap_apply])

/-- Both spectrum models use the same polynomial-to-Laurent inclusion. -/
theorem laurentSchemeIso_comp_inclusion (C : CommAlgCat.{u} R) :
    (laurentSchemeIso C).hom ≫
        AffineLine.laurentInclusion (affineTestMap C) =
      (algSpec R).map (polynomialInclusion C).op ≫ (polynomialSchemeIso C).hom := by
  apply Over.OverMorphism.ext
  change 𝟙 _ ≫ Spec.map _ = Spec.map _ ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]
  rfl

/-- The first coordinate of the Laurent product point is the constant extension. -/
theorem laurentSchemeIso_comp_fst (C : CommAlgCat.{u} R) :
    (laurentSchemeIso C).hom ≫
        AffineLine.laurentPoint (affineTestMap C) ≫ fst _ (Gm (Spec R)).X =
      (algSpec R).map (constant C).op := by
  apply Over.OverMorphism.ext
  rw [AffineLine.laurentPoint, lift_fst]
  change 𝟙 _ ≫ Spec.map (AffineLine.polynomialToLaurent (CommRingCat.of C)) ≫
      Spec.map (AffineLine.polynomialC (CommRingCat.of C)) = Spec.map _
  rw [Category.id_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change Polynomial.toLaurent (Polynomial.C c) = LaurentPolynomial.C c
  rw [Polynomial.toLaurent_C]

/-- The second coordinate of the Laurent product point is the universal unit. -/
theorem laurentSchemeIso_comp_snd (C : CommAlgCat.{u} R) :
    (laurentSchemeIso C).hom ≫
        AffineLine.laurentPoint (affineTestMap C) ≫ snd _ (Gm (Spec R)).X =
      unitPoint (universal C) := by
  apply (Gm.affinePointsEquiv ((algSpec R).obj (op (laurentAlgebra C))).hom).injective
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, AffineLine.laurentPoint, lift_snd,
    Gm.pointsEquiv_naturality, MulEquiv.apply_symm_apply, unitPoint,
    MulEquiv.apply_symm_apply]
  change (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial C))).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial C))).inv
        (LaurentPolynomial.T 1)) = LaurentPolynomial.T 1
  exact Iso.inv_hom_id_apply _ _

/-- The actual negative-coefficient ideal of a natural action. -/
abbrev attractingIdeal (a : Action B) : Ideal B := negIdeal (coaction a).hom.toRingHom

/-- Negative-ideal vanishing is exactly the existence of a polynomial orbit. -/
theorem attractingIdeal_le_ker_iff (a : Action B) (x : B ⟶ C) :
    attractingIdeal a ≤ RingHom.ker x.hom.toRingHom ↔
      ∃ θ : B ⟶ polynomialAlgebra C,
        θ ≫ polynomialInclusion C = coaction a ≫ coefficientMap x := by
  constructor
  · intro hx
    let g := coaction a ≫ coefficientMap x
    have hg : ∀ b, ∀ n < 0, (g.hom b).coeff n = 0 := by
      intro b n hn
      rw [show (g.hom b).coeff n = x.hom (((coaction a).hom b).coeff n) from
        coefficientMap_coeff x _ n]
      exact hx (Ideal.subset_span ⟨b, n, hn, rfl⟩)
    let θ : B ⟶ polynomialAlgebra C := CommAlgCat.ofHom
      { polynomialLift g.hom.toRingHom hg with
        commutes' := fun r => Polynomial.toLaurent_injective (by
          change Polynomial.toLaurent
            (polynomialLift g.hom.toRingHom hg (algebraMap R B r)) = _
          rw [toLaurent_polynomialLift]
          change g.hom (algebraMap R B r) = Polynomial.toLaurent _
          rw [g.hom.commutes]
          change LaurentPolynomial.C (algebraMap R C r) =
            Polynomial.toLaurent (Polynomial.C (algebraMap R C r))
          rw [Polynomial.toLaurent_C]) }
    refine ⟨θ, ?_⟩
    apply CommAlgCat.hom_ext
    exact AlgHom.ext (toLaurent_polynomialLift g.hom.toRingHom hg)
  · rintro ⟨θ, hθ⟩
    apply Ideal.span_le.mpr
    rintro b ⟨b', n, hn, rfl⟩
    change x.hom (((coaction a).hom b').coeff n) = 0
    rw [← coefficientMap_coeff x]
    change ((coaction a ≫ coefficientMap x).hom b').coeff n = 0
    rw [← hθ]
    exact AffineLine.coeff_toLaurent_of_neg _ hn

/-- The coordinate quotient that represents attraction. -/
abbrev attractingAlgebra (a : Action B) : CommAlgCat.{u} R :=
  CommAlgCat.of R (B ⧸ attractingIdeal a)

/-- The coordinate projection onto the attracting algebra. -/
abbrev attractingQuotient (a : Action B) : B ⟶ attractingAlgebra a :=
  CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (attractingIdeal a))

/-- The polynomial orbit associated to any point satisfying the attracting equations. -/
def polynomialOrbit (a : Action B) (x : B ⟶ C)
    (hx : attractingIdeal a ≤ RingHom.ker x.hom.toRingHom) : B ⟶ polynomialAlgebra C :=
  ((attractingIdeal_le_ker_iff a x).mp hx).choose

/-- Its restriction to the Laurent variable is the original actual coaction orbit. -/
theorem polynomialOrbit_comp (a : Action B) (x : B ⟶ C)
    (hx : attractingIdeal a ≤ RingHom.ker x.hom.toRingHom) :
    polynomialOrbit a x hx ≫ polynomialInclusion C = coaction a ≫ coefficientMap x :=
  ((attractingIdeal_le_ker_iff a x).mp hx).choose_spec

/-- Its polynomial coefficients are the images of the homogeneous coefficients. -/
theorem polynomialOrbit_coeff (a : Action B) (x : B ⟶ C)
    (hx : attractingIdeal a ≤ RingHom.ker x.hom.toRingHom) (b : B) (n : ℕ) :
    ((polynomialOrbit a x hx).hom b).coeff n =
      x.hom (((coaction a).hom b).coeff (n : ℤ)) := by
  have h := congrArg (fun f : B ⟶ laurentAlgebra C => (f.hom b).coeff (n : ℤ))
    (polynomialOrbit_comp a x hx)
  change (Polynomial.toLaurent ((polynomialOrbit a x hx).hom b)).coeff (n : ℤ) = _ at h
  rw [AffineLine.coeff_toLaurent_natCast] at h
  exact h.trans (coefficientMap_coeff x _ _)

variable {X : Over (Spec R)} [IsAffine X.left]
  (s : PointwiseSchemeAction (Gm (Spec R)).toGrp X)

/-- The coordinate coaction orbit is the actual orbit on the Laurent product test. -/
theorem pointEquiv_coaction_orbit {C : CommAlgCat.{u} R}
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    AffineSchemeCoordinates.pointEquiv X (laurentAlgebra C)
        (coaction (ofPointwiseSchemeAction s) ≫ coefficientMap x) =
      (laurentSchemeIso C).hom ≫
        AffineLine.laurentPoint (affineTestMap C) ≫
          s.orbit (AffineSchemeCoordinates.pointEquiv X C x) := by
  rw [← act_universal, pointEquiv_schemeAct, AffineSchemeCoordinates.pointEquiv_comp]
  rw [← laurentSchemeIso_comp_fst, ← laurentSchemeIso_comp_snd]
  simp only [PointwiseSchemeAction.orbit, s.naturality, Category.assoc]

/-- On every algebra spectrum, attraction is exactly vanishing of the negative ideal. -/
theorem attractingIdeal_le_ker_iff_schemeAction {C : CommAlgCat.{u} R}
    (x : AffineSchemeCoordinates.algebra X ⟶ C) :
    attractingIdeal (ofPointwiseSchemeAction s) ≤ RingHom.ker x.hom.toRingHom ↔
      s.IsAttracted (AffineSchemeCoordinates.pointEquiv X C x) := by
  rw [attractingIdeal_le_ker_iff]
  constructor
  · rintro ⟨θ, hθ⟩
    let e := (polynomialSchemeIso C).inv ≫
      AffineSchemeCoordinates.pointEquiv X (polynomialAlgebra C) θ
    have he : AffineLine.laurentInclusion (affineTestMap C) ≫ e =
        AffineLine.laurentPoint (affineTestMap C) ≫
          s.orbit (AffineSchemeCoordinates.pointEquiv X C x) := by
      apply (cancel_epi (laurentSchemeIso C).hom).mp
      dsimp only [e]
      rw [← Category.assoc, laurentSchemeIso_comp_inclusion]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [← AffineSchemeCoordinates.pointEquiv_comp, hθ, pointEquiv_coaction_orbit]
    exact ⟨AffineLine.polynomialPointInv (affineTestMap C) ≫ e,
      AffineLine.whiskerLeft_comp_of_laurentInclusion (affineTestMap C) he⟩
  · rintro ⟨E, hE⟩
    let θ := (AffineSchemeCoordinates.pointEquiv X (polynomialAlgebra C)).symm
      ((polynomialSchemeIso C).hom ≫ AffineLine.polynomialPoint (affineTestMap C) ≫ E)
    refine ⟨θ, ?_⟩
    apply (AffineSchemeCoordinates.pointEquiv X (laurentAlgebra C)).injective
    rw [AffineSchemeCoordinates.pointEquiv_comp]
    change (algSpec R).map (polynomialInclusion C).op ≫
      AffineSchemeCoordinates.pointEquiv X (polynomialAlgebra C)
        ((AffineSchemeCoordinates.pointEquiv X (polynomialAlgebra C)).symm _) = _
    rw [Equiv.apply_symm_apply, ← Category.assoc, ← laurentSchemeIso_comp_inclusion]
    simp only [Category.assoc]
    rw [AffineLine.laurentInclusion_comp_of_whiskerLeft (affineTestMap C) hE,
      pointEquiv_coaction_orbit]

/-- The actual attracting coefficient ideal of the supplied scheme action. -/
abbrev schemeActionAttractingIdeal : Ideal (AffineSchemeCoordinates.algebra X) :=
  attractingIdeal (ofPointwiseSchemeAction s)

/-- The constructed relative affine attracting scheme. -/
abbrev schemeActionAttractingScheme : Over (Spec R) :=
  AffineSchemeCoordinates.quotientScheme X (schemeActionAttractingIdeal s)

/-- Its closed inclusion into the supplied target scheme. -/
abbrev schemeActionAttractingHom : schemeActionAttractingScheme s ⟶ X :=
  AffineSchemeCoordinates.quotientHom X (schemeActionAttractingIdeal s)

/-- The attracting inclusion has an actual affine-line orbit extension. -/
theorem schemeActionAttractingHom_isAttracted :
    s.IsAttracted (schemeActionAttractingHom s) := by
  apply (attractingIdeal_le_ker_iff_schemeAction s
    (AffineSchemeCoordinates.quotientMap X (schemeActionAttractingIdeal s))).mp
  change schemeActionAttractingIdeal s ≤
    RingHom.ker (Ideal.Quotient.mk (schemeActionAttractingIdeal s))
  rw [Ideal.mk_ker]

/-- The attracting inclusion represents orbit extension on algebra spectra. -/
theorem exists_schemeActionAttracting_factor_iff {C : CommAlgCat.{u} R}
    (x : (algSpec R).obj (op C) ⟶ X) :
    (∃ y : (algSpec R).obj (op C) ⟶ schemeActionAttractingScheme s,
      y ≫ schemeActionAttractingHom s = x) ↔ s.IsAttracted x := by
  let φ := (AffineSchemeCoordinates.pointEquiv X C).symm x
  have hφ : AffineSchemeCoordinates.pointEquiv X C φ = x :=
    Equiv.apply_symm_apply _ _
  rw [← hφ, AffineSchemeCoordinates.exists_quotient_factor_iff,
    attractingIdeal_le_ker_iff_schemeAction]

/-- The same representation on an arbitrary affine relative scheme. -/
theorem exists_schemeActionAttracting_factor_iff_of_affine
    {T : Over (Spec R)} [IsAffine T.left] (x : T ⟶ X) :
    (∃ y : T ⟶ schemeActionAttractingScheme s,
      y ≫ schemeActionAttractingHom s = x) ↔ s.IsAttracted x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact PointwiseSchemeAction.IsAttracted.comp s (schemeActionAttractingHom_isAttracted s) y
  · intro hx
    let e := AffineSchemeCoordinates.schemeIso T
    obtain ⟨y, hy⟩ := (exists_schemeActionAttracting_factor_iff s (e.hom ≫ x)).mpr
      (PointwiseSchemeAction.IsAttracted.comp s hx e.hom)
    exact ⟨e.inv ≫ y, by simp only [Category.assoc, hy, e.inv_hom_id_assoc]⟩

/-- The actual closed attracting scheme represents extension on every relative test. -/
theorem exists_schemeActionAttracting_factor_iff_all
    {T : Over (Spec R)} (x : T ⟶ X) :
    (∃ y : T ⟶ schemeActionAttractingScheme s,
      y ≫ schemeActionAttractingHom s = x) ↔ s.IsAttracted x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact PointwiseSchemeAction.IsAttracted.comp s (schemeActionAttractingHom_isAttracted s) y
  · intro hx
    obtain ⟨y, hy⟩ := Langlands.AlgebraicGeometry.exists_lift_of_openCover
      (schemeActionAttractingHom s).left x.left T.left.affineCover (fun i => by
        let U : Over (Spec R) := Over.mk (T.left.affineCover.f i ≫ T.hom)
        let b : U ⟶ T := Over.homMk (T.left.affineCover.f i)
        have : IsAffine U.left := by
          change IsAffine (T.left.affineCover.X i)
          infer_instance
        obtain ⟨z, hz⟩ :=
          (exists_schemeActionAttracting_factor_iff_of_affine s (b ≫ x)).mpr
            (PointwiseSchemeAction.IsAttracted.comp s hx b)
        exact ⟨z.left, congrArg (fun f => f.left) hz⟩)
    refine ⟨Over.homMk y ?_, ?_⟩
    · rw [← (schemeActionAttractingHom s).w, ← Category.assoc, hy, x.w]
    · apply Over.OverMorphism.ext
      exact hy

/-- The universal affine-line extension of the attracting inclusion. -/
def schemeActionAttractingExtension :
    schemeActionAttractingScheme s ⊗ AffineLine.scheme (Spec R) ⟶ X :=
  (schemeActionAttractingHom_isAttracted s).choose

/-- The universal extension restricts to the orbit of the actual inclusion. -/
theorem schemeActionAttractingExtension_restrict :
    schemeActionAttractingScheme s ◁ AffineLine.unitInclusion (Spec R) ≫
        schemeActionAttractingExtension s = s.orbit (schemeActionAttractingHom s) :=
  (schemeActionAttractingHom_isAttracted s).choose_spec

/-- The attracting coordinate quotient of a smooth algebra is smooth over any base. -/
theorem smooth_attractingAlgebra (a : Action B) [Algebra.Smooth R B] :
    Algebra.Smooth R (attractingAlgebra a) := by
  have hc : ∀ b : B, (((coaction a).hom b).coeff.sum fun _ b' => b') = b := by
    intro b
    have h := congrArg (fun f : B ⟶ B => f.hom b) (coaction_counit a)
    change LaurentPolynomial.eval₂ (RingHom.id B) 1 ((coaction a).hom b) = b at h
    exact (AffineLine.eval₂_id_one (A := CommRingCat.of B)
      ((coaction a).hom b)).symm.trans h
  exact DynamicSmoothRing.smooth_quotient_of_fg
    (negIdeal_fg (R := R) (coaction a).hom.toRingHom (coaction_scalar a))
    (formallySmooth_quotient_negIdeal (coaction_scalar a) hc
      (coaction_coefficient_homogeneous a))

/-- The attracting scheme of a smooth affine scheme is smooth over the base. -/
theorem smooth_schemeActionAttractingScheme (hX : Smooth X.hom) :
    Smooth (schemeActionAttractingScheme s).hom := by
  let := AffineSchemeCoordinates.smooth_algebra X hX
  let := smooth_attractingAlgebra (ofPointwiseSchemeAction s)
  have h : Smooth (Spec.map (CommRingCat.ofHom
      (algebraMap R (attractingAlgebra (ofPointwiseSchemeAction s))))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact h

end GmCoordinateAction

end Langlands.GroupScheme
