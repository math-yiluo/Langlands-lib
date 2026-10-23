import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Flat.Localization
import Mathlib.Algebra.Category.Ring.Instances
import Langlands.AlgebraicGeometry.FiberStalkFlatnessStatement

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

namespace FiberStalkFlatness

/-- In `CommRingCat`, the cobase change of a localization is a localization. -/
lemma isLocalization_of_isPushout {A₀ A C F : CommRingCat.{u}} {a : A₀ ⟶ A} {b : A₀ ⟶ C}
    {c : A ⟶ F} {d : C ⟶ F} (h : IsPushout a b c d) (M : Submonoid A₀)
    (hA : letI := a.hom.toAlgebra; IsLocalization M A) :
    letI := d.hom.toAlgebra; IsLocalization (M.map b.hom) F := by
  let := a.hom.toAlgebra
  let := b.hom.toAlgebra
  let := c.hom.toAlgebra
  let := d.hom.toAlgebra
  let : Algebra A₀ F := (a ≫ c).hom.toAlgebra
  have : IsScalarTower A₀ A F := .of_algebraMap_eq' rfl
  have : IsScalarTower A₀ C F := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom h.w)
  have := hA
  have h' : Algebra.IsPushout A₀ C A F := CommRingCat.isPushout_iff_isPushout.mp h.flip
  exact (Algebra.isLocalization_iff_isPushout M A).mpr h'

/-- Flatness passes along a commutative square whose vertical maps are localizations. -/
lemma flat_of_isLocalization_square {C D F G : CommRingCat.{u}} (φ : C ⟶ D) (l : C ⟶ F)
    (m : D ⟶ G) (ψ : F ⟶ G) (hφ : φ.hom.Flat) (w : φ ≫ m = l ≫ ψ)
    (M : Submonoid C) (N : Submonoid D)
    (hl : letI := l.hom.toAlgebra; IsLocalization M F)
    (hm : letI := m.hom.toAlgebra; IsLocalization N G) : ψ.hom.Flat := by
  let := φ.hom.toAlgebra
  let := l.hom.toAlgebra
  let := m.hom.toAlgebra
  let := ψ.hom.toAlgebra
  let : Algebra C G := (l ≫ ψ).hom.toAlgebra
  have : IsScalarTower C D G := .of_algebraMap_eq' (congrArg CommRingCat.Hom.hom w.symm)
  have : IsScalarTower C F G := .of_algebraMap_eq' rfl
  have := hl
  have := hm
  have : Module.Flat C D := hφ
  have : Module.Flat D G := IsLocalization.flat G N
  have : Module.Flat C G := Module.Flat.trans C D G
  exact (Module.flat_iff_of_isLocalization F M G).mpr this

/-- The germ of a section followed by a stalk map is the germ of its `appLE` image. -/
lemma germ_stalkMap_eq_appLE_germ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V) (hfx : f x ∈ U) :
    Y.presheaf.germ U (f x) hfx ≫ f.stalkMap x = f.appLE U V e ≫ X.presheaf.germ V x hx := by
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]

lemma appLE_eq_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (U : Y.Opens) (V : X.Opens)
    (e : V ≤ f ⁻¹ᵁ U) : f.appLE U V e = g.appLE U V (h ▸ e) := by
  subst h
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma SpecMap_appLE_top_top {A B : CommRingCat.{u}} (r : A ⟶ B)
    (e : (⊤ : (Spec B).Opens) ≤ Spec.map r ⁻¹ᵁ ⊤) :
    (Spec.map r).appLE ⊤ ⊤ e = (Spec.map r).appTop := by
  rw [Scheme.Hom.appLE, show (homOfLE e).op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- On sections, `Spec κ(s) ⟶ S` is the germ at `s` followed by the residue map. -/
lemma fromSpecResidueField_appLE {S : Scheme.{u}} (US : S.Opens) (s : S) (hs : s ∈ US)
    (e : (⊤ : (Spec (S.residueField s)).Opens) ≤ S.fromSpecResidueField s ⁻¹ᵁ US) :
    (S.fromSpecResidueField s).appLE US ⊤ e ≫ (Scheme.ΓSpecIso (S.residueField s)).hom =
      S.presheaf.germ US s hs ≫ S.residue s := by
  rw [appLE_eq_of_eq (Scheme.fromSpecResidueField.eq_1 S s), Scheme.Hom.comp_appLE,
    Scheme.fromSpecStalk_app hs]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc, SpecMap_appLE_top_top, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc]

/-- Over an affine open, the germ at `s` and the residue map form a pushout square with
`Spec κ(s) ⟶ S`. -/
lemma isPushout_residue {S : Scheme.{u}} {US : S.Opens} (hUS : IsAffineOpen US) (s : S)
    (hs : s ∈ US)
    (e : (⊤ : (Spec (S.residueField s)).Opens) ≤ S.fromSpecResidueField s ⁻¹ᵁ US) :
    IsPushout (S.presheaf.germ US s hs) ((S.fromSpecResidueField s).appLE US ⊤ e)
      (S.residue s) (Scheme.ΓSpecIso (S.residueField s)).hom := by
  have : Epi (S.presheaf.germ US s hs) := by
    let := TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨s, hs⟩
    have := hUS.isLocalization_stalk ⟨s, hs⟩
    exact IsLocalization.epi (hUS.primeIdealOf ⟨s, hs⟩).asIdeal.primeCompl (S.presheaf.stalk s)
  exact IsPushout.of_horiz_isIso_epi ⟨(fromSpecResidueField_appLE US s hs e).symm⟩

set_option backward.isDefEq.respectTransparency false in
/-- The algebraic core. Two pushout squares of sections `PY`, `PX` over the same base change
`gK : a₀ ⟶ K`, a flat map `φ` between their pushouts compatible with `u : aY ⟶ aX`, the residue
square `Q1`, and localizations `γY : aY ⟶ A`, `γX : aX ⟶ B` compatible with `α : R ⟶ A`,
`β : A ⟶ B` give flatness of `F ⊗[A] B` over `F = A ⊗[R] k`. -/
lemma flat_of_sections {a₀ K aY aX ΓY ΓX R A B : CommRingCat.{u}} {k : Type u} [CommRing k]
    [Algebra R k] {tY : a₀ ⟶ aY} {gK : a₀ ⟶ K} {iY : aY ⟶ ΓY} {jY : K ⟶ ΓY}
    (PY : IsPushout tY gK iY jY) {tX : a₀ ⟶ aX} {iX : aX ⟶ ΓX} {jX : K ⟶ ΓX}
    (PX : IsPushout tX gK iX jX) (u : aY ⟶ aX) (hu : tY ≫ u = tX)
    (φ : ΓY ⟶ ΓX) (hφ : φ.hom.Flat) (hφ₁ : iY ≫ φ = u ≫ iX) (hφ₂ : jY ≫ φ = jX)
    {r : a₀ ⟶ R} {e : K ⟶ CommRingCat.of k}
    (Q1 : IsPushout r gK (CommRingCat.ofHom (algebraMap R k)) e)
    (α : R ⟶ A) (β : A ⟶ B) (γY : aY ⟶ A) (γX : aX ⟶ B) (hα : r ≫ α = tY ≫ γY)
    (hβ : γY ≫ β = u ≫ γX) (MY : Submonoid aY) (MX : Submonoid aX)
    (hγY : letI := γY.hom.toAlgebra; IsLocalization MY A)
    (hγX : letI := γX.hom.toAlgebra; IsLocalization MX B) :
    letI := α.hom.toAlgebra
    letI := β.hom.toAlgebra
    Module.Flat (A ⊗[R] k) ((A ⊗[R] k) ⊗[A] B) := by
  let := α.hom.toAlgebra
  let := β.hom.toAlgebra
  have Q2 := CommRingCat.isPushout_tensorProduct R A k
  have Q3 := (CommRingCat.isPushout_tensorProduct A (A ⊗[R] k) B).flip
  have OY : IsPushout (tY ≫ γY) gK
      (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := k)))
      (e ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A)
        (B := k)).toRingHom) := by
    rw [← hα]
    exact Q1.paste_horiz Q2
  have OX : IsPushout (tX ≫ γX) gK
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := A) (A := A ⊗[R] k)
        (B := B)).toRingHom)
      ((e ≫ CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A)
        (B := k)).toRingHom) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A ⊗[R] k)
          (B := B))) := by
    rw [← hu, Category.assoc, ← hβ, ← Category.assoc]
    exact OY.paste_horiz Q3
  have TY := IsPushout.of_left' OY PY
  have TX := IsPushout.of_left' OX PX
  have hl := isLocalization_of_isPushout TY MY hγY
  have hm := isLocalization_of_isPushout TX MX hγX
  have w : φ ≫ PX.desc (γX ≫ _) _ (by rw [← Category.assoc, OX.w]) =
      PY.desc (γY ≫ _) _ (by rw [← Category.assoc, OY.w]) ≫
        CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := A) (A := A ⊗[R] k)
          (B := B)) := by
    apply PY.hom_ext
    · rw [← Category.assoc, hφ₁, Category.assoc, PX.inl_desc, PY.inl_desc_assoc,
        ← Category.assoc, ← hβ, Category.assoc, Category.assoc]
      exact congrArg (γY ≫ ·) Q3.w
    · rw [← Category.assoc, hφ₂, PX.inr_desc, ← Category.assoc, PY.inr_desc]
  have hψ := flat_of_isLocalization_square φ _ _ _ hφ w _ _ hl hm
  rw [← RingHom.flat_algebraMap_iff]
  exact hψ

set_option backward.isDefEq.respectTransparency false in
/-- The bridge for arbitrary pullback squares of `πX = p ≫ q` and `q` along
`Spec κ(s) ⟶ S`, with a flat map `fs` between the two fibres over `p`. -/
lemma flat_fiber_stalk {S X Y Xs Ys : Scheme.{u}} (p : X ⟶ Y) (q : Y ⟶ S) (πX : X ⟶ S)
    (hw : p ≫ q = πX) (x : X)
    {aX : Xs ⟶ X} {bX : Xs ⟶ Spec (S.residueField (q (p x)))}
    {aY : Ys ⟶ Y} {bY : Ys ⟶ Spec (S.residueField (q (p x)))}
    (HX : IsPullback aX bX πX (S.fromSpecResidueField (q (p x))))
    (HY : IsPullback aY bY q (S.fromSpecResidueField (q (p x))))
    (fs : Xs ⟶ Ys) (h₁ : fs ≫ aY = aX ≫ p) (h₂ : fs ≫ bY = bX) [Flat fs] :
    letI := (q.stalkMap (p x)).hom.toAlgebra
    letI := (p.stalkMap x).hom.toAlgebra
    Module.Flat (Y.presheaf.stalk (p x) ⊗[S.presheaf.stalk (q (p x))]
        IsLocalRing.ResidueField (S.presheaf.stalk (q (p x))))
      ((Y.presheaf.stalk (p x) ⊗[S.presheaf.stalk (q (p x))]
        IsLocalRing.ResidueField (S.presheaf.stalk (q (p x)))) ⊗[Y.presheaf.stalk (p x)]
          X.presheaf.stalk x) := by
  subst hw
  obtain ⟨US, hUS, hsUS, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := q (p x)) (by simp)
  obtain ⟨UY, hUY, hyUY, hYS⟩ :=
    exists_isAffineOpen_mem_and_subset (U := q ⁻¹ᵁ US) (x := p x) hsUS
  obtain ⟨UX, hUX, hxUX, hXY⟩ :=
    exists_isAffineOpen_mem_and_subset (U := p ⁻¹ᵁ UY) (x := x) hyUY
  have hT : (⊤ : (Spec (S.residueField (q (p x)))).Opens) ≤
      S.fromSpecResidueField (q (p x)) ⁻¹ᵁ US := fun t _ => by
    simpa [Scheme.fromSpecResidueField_apply] using hsUS
  have hYS' : UY ≤ q ⁻¹ᵁ US := hYS
  have hXY' : UX ≤ p ⁻¹ᵁ UY := hXY
  have hXS : UX ≤ (p ≫ q) ⁻¹ᵁ US := fun z hz => hYS' (hXY' hz)
  have : IsAffine _ := hUS
  have : IsAffine _ := hUY
  have : IsAffine _ := hUX
  have : IsAffine _ := isAffineOpen_top (Spec (S.residueField (q (p x))))
  have hUYs : IsAffineOpen (aY ⁻¹ᵁ UY ⊓ bY ⁻¹ᵁ ⊤) :=
    IsAffine.of_isIso (Scheme.Hom.isPullback_resLE HY hT hYS' rfl).isoPullback.hom
  have hUXs : IsAffineOpen (aX ⁻¹ᵁ UX ⊓ bX ⁻¹ᵁ ⊤) :=
    IsAffine.of_isIso (Scheme.Hom.isPullback_resLE HX hT hXS rfl).isoPullback.hom
  have hle : aX ⁻¹ᵁ UX ⊓ bX ⁻¹ᵁ ⊤ ≤ fs ⁻¹ᵁ (aY ⁻¹ᵁ UY ⊓ bY ⁻¹ᵁ ⊤) := by
    intro z hz
    refine ⟨?_, trivial⟩
    show aY (fs z) ∈ UY
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
    exact hXY' hz.1
  have PY := (isIso_pushoutSection_iff HY hT hYS' rfl).mp
    (isIso_pushoutSection_of_isAffineOpen HY hT hYS' rfl hUS (isAffineOpen_top _) hUY)
  have PX := (isIso_pushoutSection_iff HX hT hXS rfl).mp
    (isIso_pushoutSection_of_isAffineOpen HX hT hXS rfl hUS (isAffineOpen_top _) hUX)
  exact flat_of_sections (k := IsLocalRing.ResidueField (S.presheaf.stalk (q (p x))))
    PY PX (p.appLE UY UX hXY') (Scheme.Hom.appLE_comp_appLE ..)
    (fs.appLE _ _ hle) (fs.flat_appLE hUYs hUXs hle)
    (by rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]; exact appLE_eq_of_eq h₁ ..)
    (by rw [Scheme.Hom.appLE_comp_appLE]; exact appLE_eq_of_eq h₂ ..)
    (isPushout_residue hUS (q (p x)) hsUS hT)
    (q.stalkMap (p x)) (p.stalkMap x) (Y.presheaf.germ UY (p x) hyUY)
    (X.presheaf.germ UX x hxUX)
    (germ_stalkMap_eq_appLE_germ q US UY hYS' (p x) hyUY hsUS)
    (germ_stalkMap_eq_appLE_germ p UY UX hXY' x hxUX hyUY)
    _ _ (hUY.isLocalization_stalk ⟨p x, hyUY⟩) (hUX.isLocalization_stalk ⟨x, hxUX⟩)

end FiberStalkFlatness

open FiberStalkFlatness in
/-- The scheme-fibre to stalk-base-change flatness bridge. -/
theorem fiberStalkFlatness : FiberStalkFlatnessStatement.{u} := by
  intro S X Y f x y s R A B k F hflat
  exact flat_fiber_stalk f.left Y.hom X.hom (Over.w f) x (IsPullback.of_hasPullback _ _)
    (IsPullback.of_hasPullback _ _) ((Over.pullback (S.fromSpecResidueField s)).map f).left
    (by simp only [Over.pullback_map_left]; exact pullback.lift_fst _ _ _)
    (by simp only [Over.pullback_map_left]; exact pullback.lift_snd _ _ _)

end Langlands.AlgebraicGeometry
