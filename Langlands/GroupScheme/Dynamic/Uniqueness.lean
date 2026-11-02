import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.MultiplicativeLaurent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Uniqueness of orbit extensions for separated group schemes

For every scheme `T` over `S`, two morphisms `T ×_S 𝔸¹_S ⟶ Y` to a separated `S`-scheme `Y`
that agree on `T ×_S 𝔾_{m,S}` are equal. Consequently, for a separated group scheme `G` and a
cocharacter `χ`, an extension of an orbit map is unique, the limit of a point is unique, and the
limit lies in the centralizer `Z_G(χ)`.

No flatness of `T` is needed: over an affine open `Spec A` of `T`, the point
`Spec A[X] ⟶ Spec A ×_S 𝔸¹_S` is a split epimorphism, and `Spec A[X, X⁻¹] ⟶ Spec A[X]` is
scheme-theoretically dominant because `A[X] ⟶ A[X, X⁻¹]` is injective.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- Two morphisms that agree after a separated morphism `s` and after a scheme-theoretically
dominant morphism `j` are equal. -/
theorem ext_of_isSchemeTheoreticallyDominant {W X Y Z : Scheme.{u}} {f g : X ⟶ Y}
    (s : Y ⟶ Z) [IsSeparated s] (h : f ≫ s = g ≫ s) (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] (hj : j ≫ f = j ≫ g) : f = g := by
  let X' : Over Z := Over.mk (f ≫ s)
  let Y' : Over Z := Over.mk s
  let W' : Over Z := Over.mk (j ≫ f ≫ s)
  let f' : X' ⟶ Y' := Over.homMk f rfl
  let g' : X' ⟶ Y' := Over.homMk g h.symm
  let j' : W' ⟶ X' := Over.homMk j rfl
  have : IsSeparated Y'.hom := ‹_›
  have hl : j' ≫ f' = j' ≫ g' := Over.OverMorphism.ext hj
  have hcomp : (equalizer.lift j' hl).left ≫ (equalizer.ι f' g').left = j := by
    rw [← Over.comp_left, equalizer.lift_ι]
    rfl
  have hker : (equalizer.ι f' g').left.ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp (equalizer.lift j' hl).left _).trans ?_)
    rw [hcomp, j.ker_eq_bot]
  have : IsIso (equalizer.ι f' g').left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)

/-- The spectrum of an injective ring homomorphism is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_specMap {A B : CommRingCat.{u}} {φ : A ⟶ B}
    (hφ : Function.Injective φ) : IsSchemeTheoreticallyDominant (Spec.map φ) := by
  have hinj : Function.Injective (Spec.map φ).appTop := by
    intro x y hxy
    have h := congrArg (Scheme.ΓSpecIso B).hom hxy
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality,
      CommRingCat.comp_apply, CommRingCat.comp_apply] at h
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).1 (hφ h)
  rw [isSchemeTheoreticallyDominant_iff, Scheme.ker_of_isAffine,
    (RingHom.injective_iff_ker_eq_bot _).mp hinj,
    ← Scheme.IdealSheafData.equivOfIsAffine_symm_apply, map_bot]

namespace AffineLine

section Polynomial

variable {A : CommRingCat.{u}} (f : Spec A ⟶ S)

variable (A) in
/-- The constants `A ⟶ A[X]`. -/
abbrev polynomialC : A ⟶ CommRingCat.of (Polynomial A) :=
  CommRingCat.ofHom Polynomial.C

variable (A) in
/-- The inclusion `A[X] ⟶ A[X, X⁻¹]`. -/
abbrev polynomialToLaurent :
    CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (LaurentPolynomial A) :=
  CommRingCat.ofHom Polynomial.toLaurent

/-- `Spec A[X]` as a scheme over `S`, through `Spec A`. -/
abbrev polynomialScheme : Over S :=
  Over.mk (Spec.map (polynomialC A) ≫ f)

/-- The projection `Spec A[X] ⟶ Spec A` over `S`. -/
def polynomialProj : polynomialScheme f ⟶ Over.mk f :=
  Over.homMk (Spec.map (polynomialC A)) rfl

/-- The point `(Spec A[X] → Spec A, X)` of `Spec A ×_S 𝔸¹_S`. -/
def polynomialPoint : polynomialScheme f ⟶ Over.mk f ⊗ scheme S :=
  lift (polynomialProj f) ((homEquiv _).symm ((Scheme.ΓSpecIso _).inv Polynomial.X))

/-- The ring homomorphism `A[X] ⟶ Γ(Spec A ×_S 𝔸¹_S)` sending `a` to its pullback along the
first projection and `X` to the coordinate. -/
def polynomialSections :
    CommRingCat.of (Polynomial A) ⟶ Γ((Over.mk f ⊗ scheme S).left, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom
    (Gm.specHomEquiv _ A (fst (Over.mk f) (scheme S)).left).hom
    (homEquiv _ (snd (Over.mk f) (scheme S))))

theorem polynomialC_comp_polynomialSections :
    polynomialC A ≫ polynomialSections f = Gm.specHomEquiv _ A (fst (Over.mk f) (scheme S)).left := by
  ext a
  simp [polynomialSections]

theorem polynomialSections_X :
    polynomialSections f Polynomial.X = homEquiv _ (snd (Over.mk f) (scheme S)) := by
  simp [polynomialSections]

/-- The underlying morphism of the inverse of `polynomialPoint`. -/
def polynomialPointInvLeft : (Over.mk f ⊗ scheme S).left ⟶ Spec (CommRingCat.of (Polynomial A)) :=
  (Gm.specHomEquiv _ _).symm (polynomialSections f)

theorem polynomialPointInvLeft_comp :
    polynomialPointInvLeft f ≫ Spec.map (polynomialC A) = (fst (Over.mk f) (scheme S)).left := by
  have h : polynomialPointInvLeft f ≫ Spec.map (polynomialC A) =
      (Gm.specHomEquiv _ _).symm (polynomialC A ≫ polynomialSections f) := by
    simp only [polynomialPointInvLeft, Gm.specHomEquiv, Equiv.coe_fn_symm_mk, Category.assoc,
      Spec.map_comp]
  rw [h, polynomialC_comp_polynomialSections, Equiv.symm_apply_apply]

/-- The inverse of `polynomialPoint`. -/
def polynomialPointInv : Over.mk f ⊗ scheme S ⟶ polynomialScheme f :=
  Over.homMk (polynomialPointInvLeft f) (by
    change polynomialPointInvLeft f ≫ Spec.map (polynomialC A) ≫ f = _
    rw [← Category.assoc, polynomialPointInvLeft_comp]
    exact Over.w (fst (Over.mk f) (scheme S)))

theorem polynomialPointInv_comp_polynomialProj :
    polynomialPointInv f ≫ polynomialProj f = fst (Over.mk f) (scheme S) :=
  Over.OverMorphism.ext (polynomialPointInvLeft_comp f)

theorem homEquiv_polynomialPointInv_comp_snd :
    homEquiv _ (polynomialPointInv f ≫ (homEquiv _).symm ((Scheme.ΓSpecIso _).inv Polynomial.X)) =
      homEquiv _ (snd (Over.mk f) (scheme S)) := by
  rw [homEquiv_comp, Equiv.apply_symm_apply, ← polynomialSections_X]
  change Gm.specHomEquiv _ _ (polynomialPointInvLeft f) Polynomial.X = _
  rw [polynomialPointInvLeft, Equiv.apply_symm_apply]

/-- `polynomialPoint` is a split epimorphism, with section `polynomialPointInv`. -/
theorem polynomialPointInv_comp_polynomialPoint :
    polynomialPointInv f ≫ polynomialPoint f = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, polynomialPoint, lift_fst, Category.id_comp,
      polynomialPointInv_comp_polynomialProj]
  · rw [Category.assoc, polynomialPoint, lift_snd, Category.id_comp]
    exact hom_ext (homEquiv_polynomialPointInv_comp_snd f)

/-- `Spec A[X, X⁻¹]` as a scheme over `S`, through `Spec A[X]`. -/
abbrev laurentScheme : Over S :=
  Over.mk (Spec.map (polynomialToLaurent A) ≫ (polynomialScheme f).hom)

/-- The inclusion `Spec A[X, X⁻¹] ⟶ Spec A[X]` over `S`. -/
def laurentInclusion : laurentScheme f ⟶ polynomialScheme f :=
  Over.homMk (Spec.map (polynomialToLaurent A)) rfl

/-- The unit `X` as a global unit of `Spec A[X, X⁻¹]`. -/
def laurentUnit : (Γ((laurentScheme f).left, ⊤))ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom.toMonoidHom
    (Gm.relativeCoordUnit A)

/-- On `Spec A[X, X⁻¹]`, the point `polynomialPoint` lands in `Spec A ×_S 𝔾_{m,S}`. -/
theorem laurentInclusion_polynomialPoint : laurentInclusion f ≫ polynomialPoint f =
    lift (laurentInclusion f ≫ polynomialProj f) ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫
      (Over.mk f ◁ unitInclusion S) := by
  rw [lift_whiskerLeft, polynomialPoint, comp_lift]
  congr 1
  apply hom_ext
  rw [homEquiv_comp, Equiv.apply_symm_apply, homEquiv_comp_unitInclusion,
    MulEquiv.apply_symm_apply]
  change (Spec.map (polynomialToLaurent A)).appTop ((Scheme.ΓSpecIso _).inv Polynomial.X) =
    (Scheme.ΓSpecIso _).inv (LaurentPolynomial.T 1)
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  simp [Polynomial.toLaurent_X]

end Polynomial

/-- Two morphisms `Spec A ×_S 𝔸¹_S ⟶ Y` to a separated `S`-scheme that agree on
`Spec A ×_S 𝔾_{m,S}` are equal. -/
theorem hom_ext_of_unitInclusion_affine {A : CommRingCat.{u}} (f : Spec A ⟶ S) {Y : Over S}
    [IsSeparated Y.hom] {e e' : Over.mk f ⊗ scheme S ⟶ Y}
    (h : Over.mk f ◁ unitInclusion S ≫ e = Over.mk f ◁ unitInclusion S ≫ e') : e = e' := by
  suffices hp : polynomialPoint f ≫ e = polynomialPoint f ≫ e' by
    rw [← Category.id_comp e, ← Category.id_comp e', ← polynomialPointInv_comp_polynomialPoint f,
      Category.assoc, Category.assoc, hp]
  have : IsSchemeTheoreticallyDominant (Spec.map (polynomialToLaurent A)) :=
    isSchemeTheoreticallyDominant_specMap Polynomial.toLaurent_injective
  apply Over.OverMorphism.ext
  refine ext_of_isSchemeTheoreticallyDominant Y.hom ?_ (Spec.map (polynomialToLaurent A)) ?_
  · rw [Over.w, Over.w]
  · have h2 : laurentInclusion f ≫ polynomialPoint f ≫ e =
        laurentInclusion f ≫ polynomialPoint f ≫ e' := by
      rw [← Category.assoc, laurentInclusion_polynomialPoint, Category.assoc, h,
        ← Category.assoc, ← laurentInclusion_polynomialPoint, Category.assoc]
    exact congrArg (fun k => k.left) h2

/-- The restriction of `T ×_S 𝔸¹_S` to the preimage of an open `Spec A ⟶ T`, as a map from the
pullback of the first projection. -/
def pullbackFstToWhiskerRight (T : Over S) {A : CommRingCat.{u}} (a : Spec A ⟶ T.left) :
    pullback (fst T (scheme S)).left a ⟶ (Over.mk (a ≫ T.hom) ⊗ scheme S).left :=
  pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ (snd T (scheme S)).left) (by
    change pullback.snd _ _ ≫ a ≫ T.hom = _
    rw [← Category.assoc, ← pullback.condition]
    simp only [Category.assoc]
    rw [Over.w (fst T (scheme S)), Over.w (snd T (scheme S))])

theorem pullbackFstToWhiskerRight_comp (T : Over S) {A : CommRingCat.{u}} (a : Spec A ⟶ T.left) :
    pullbackFstToWhiskerRight T a ≫
      ((Over.homMk a rfl : Over.mk (a ≫ T.hom) ⟶ T) ▷ scheme S).left = pullback.fst _ _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Over.whiskerRight_left_fst, pullbackFstToWhiskerRight,
      pullback.lift_fst_assoc]
    exact pullback.condition.symm
  · rw [Category.assoc, Over.whiskerRight_left_snd, pullbackFstToWhiskerRight, pullback.lift_snd]
    rfl

/-- Two morphisms `T ×_S 𝔸¹_S ⟶ Y` to a separated `S`-scheme that agree on `T ×_S 𝔾_{m,S}` are
equal, for every scheme `T` over `S`. -/
theorem hom_ext_of_unitInclusion {T Y : Over S} [IsSeparated Y.hom]
    {e e' : T ⊗ scheme S ⟶ Y} (h : T ◁ unitInclusion S ≫ e = T ◁ unitInclusion S ≫ e') :
    e = e' := by
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext (T.left.affineOpenCover.openCover.pullback₁ (fst T (scheme S)).left)
    _ _ fun (i : T.left.affineOpenCover.I₀) => ?_
  let a : Over.mk (T.left.affineOpenCover.f i ≫ T.hom) ⟶ T :=
    Over.homMk (T.left.affineOpenCover.f i) rfl
  have key : a ▷ scheme S ≫ e = a ▷ scheme S ≫ e' := by
    apply hom_ext_of_unitInclusion_affine
    rw [whisker_exchange_assoc, h, ← whisker_exchange_assoc]
  change pullback.fst _ (T.left.affineOpenCover.f i) ≫ e.left =
    pullback.fst _ (T.left.affineOpenCover.f i) ≫ e'.left
  rw [← pullbackFstToWhiskerRight_comp T (T.left.affineOpenCover.f i), Category.assoc,
    Category.assoc, ← Over.comp_left, ← Over.comp_left]
  exact congrArg (fun k => pullbackFstToWhiskerRight T _ ≫ k.left) key

/-- The scaling map `(T ×_S 𝔾_{m,S}) ×_S 𝔸¹_S ⟶ T ×_S 𝔸¹_S`, `((t, s), x) ↦ (t, s x)`. -/
def scale (T : Over S) : (T ⊗ (Gm S).X) ⊗ scheme S ⟶ T ⊗ scheme S :=
  lift (fst _ _ ≫ fst _ _) ((homEquiv _).symm
    (homEquiv _ (fst _ _ ≫ snd _ _ ≫ unitInclusion S) * homEquiv _ (snd _ _)))

/-- On `(T ×_S 𝔾_{m,S}) ×_S 𝔾_{m,S}`, scaling is the group law of `𝔾_{m,S}`. -/
@[reassoc]
theorem whiskerLeft_unitInclusion_scale (T : Over S) :
    (T ⊗ (Gm S).X) ◁ unitInclusion S ≫ scale T =
      lift (fst _ _ ≫ fst _ _) (fst _ _ ≫ snd _ _ * snd _ _) ≫ T ◁ unitInclusion S := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [scale]
  · apply hom_ext
    rw [Category.assoc, Category.assoc, scale, lift_snd, whiskerLeft_snd, lift_snd_assoc,
      homEquiv_comp, Equiv.apply_symm_apply, map_mul, ← homEquiv_comp, ← homEquiv_comp,
      whiskerLeft_fst_assoc, whiskerLeft_snd, homEquiv_comp_unitInclusion,
      ← Category.assoc (fst _ _) (snd _ _), homEquiv_comp_unitInclusion,
      homEquiv_comp_unitInclusion, map_mul, Units.val_mul]

/-- Scaling fixes the zero section. -/
theorem lift_zeroSection_scale (T : Over S) :
    lift (𝟙 _) (toUnit _ ≫ zeroSection S) ≫ scale T =
      fst T (Gm S).X ≫ lift (𝟙 T) (toUnit T ≫ zeroSection S) := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · simp [scale]
  · apply hom_ext
    rw [Category.assoc, Category.assoc, scale, lift_snd, lift_snd, homEquiv_comp,
      Equiv.apply_symm_apply, map_mul, ← homEquiv_comp (lift _ _) (snd _ _), lift_snd,
      homEquiv_comp_zeroSection, mul_zero, ← Category.assoc, homEquiv_comp_zeroSection]

end AffineLine

namespace Dynamic

variable {G : GroupScheme S} (χ : (Gm S).toGrp ⟶ G) [IsSeparated G.X.hom]

/-- For a separated group scheme, an orbit map has at most one extension to `T ×_S 𝔸¹_S`. -/
theorem IsOrbitExtension.unique {T : Over S} {g : T ⟶ G.X}
    {e e' : T ⊗ AffineLine.scheme S ⟶ G.X} (he : IsOrbitExtension χ g e)
    (he' : IsOrbitExtension χ g e') : e = e' :=
  AffineLine.hom_ext_of_unitInclusion (he.trans he'.symm)

/-- For a separated group scheme, a point has at most one limit. -/
theorem HasLimit.unique {T : Over S} {g l l' : T ⟶ G.X} (hl : HasLimit χ g l)
    (hl' : HasLimit χ g l') : l = l' := by
  obtain ⟨e, he, rfl⟩ := hl
  obtain ⟨e', he', rfl⟩ := hl'
  rw [he.unique χ he']

/-- For a separated group scheme, the limit of a point lies in `Z(χ)`: the extensions
`((t, s), x) ↦ χ(s) e(t, x) χ(s)⁻¹` and `((t, s), x) ↦ e(t, s x)` agree on
`(T ×_S 𝔾_{m,S}) ×_S 𝔾_{m,S}`, hence everywhere, and their values at `x = 0` are the orbit of
the limit and the limit. -/
theorem HasLimit.mem_centralizer {T : Over S} {g l : T ⟶ G.X} (hl : HasLimit χ g l) :
    l ∈ (centralizer χ).carrier T := by
  obtain ⟨e, he, rfl⟩ := hl
  let s : (T ⊗ (Gm S).X) ⊗ AffineLine.scheme S ⟶ G.X := fst _ _ ≫ snd _ _ ≫ χ.hom.hom
  have key : s * (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e) * s⁻¹ = AffineLine.scale T ≫ e := by
    apply AffineLine.hom_ext_of_unitInclusion
    rw [AffineLine.whiskerLeft_unitInclusion_scale_assoc, he, MonObj.comp_mul, MonObj.comp_mul,
      GrpObj.comp_inv, whisker_exchange_assoc, he, whiskerRight_orbit]
    simp only [s, orbit, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst_assoc, lift_fst_assoc,
      lift_snd_assoc, MonObj.mul_comp, mul_inv_rev, mul_assoc, Category.assoc]
  have h0 := congrArg evalZero key
  rw [evalZero_mul, evalZero_mul, evalZero_inv, evalZero_whiskerRight] at h0
  rw [Dynamic.mem_centralizer]
  refine Eq.trans ?_ (h0.trans ?_)
  · rw [orbit]
    simp only [s, evalZero_fst]
  · rw [evalZero, ← Category.assoc, AffineLine.lift_zeroSection_scale, Category.assoc]
    rfl

end Dynamic

end Langlands.GroupScheme
