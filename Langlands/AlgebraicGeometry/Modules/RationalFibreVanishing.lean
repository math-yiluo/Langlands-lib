import Langlands.AlgebraicGeometry.Modules.PerfectFibreVanishing
import Langlands.AlgebraicGeometry.Modules.OpenCohomologyVanishing
import Langlands.AlgebraicGeometry.Modules.SchemeIsoCohomology
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Vanishing of higher direct images from rational fibres

Whether `Hⁿ(P, N)` vanishes does not depend on the affine base `Spec R` over which it is
computed, and is invariant under isomorphisms of fibre products over `X`. If `K` is an
algebraically closed field, `g : Y ⟶ Spec K` is locally of finite type, `V` is an affine
open of `Y` and `m` is a maximal ideal of `Γ(Y, V)`, then `Spec (Γ(Y, V) ⧸ m) ⟶ Y` is a
rational point of `Y` after composing with an isomorphism `Spec K ≅ Spec (Γ(Y, V) ⧸ m)`
(Hilbert's Nullstellensatz). Vanishing of cohomology on the fibre of `f` over such a rational
point gives vanishing on the fibre of `f⁻¹ V ⟶ Spec Γ(Y, V)` over `Spec (Γ(Y, V) ⧸ m)`.

Combining these with the published affine-open detection of higher direct images and the
quotient-fibre criterion, assuming `UniversalPerfectSectionsStatement` as a hypothesis: for a
smooth proper `f : X ⟶ Y` and a line bundle `Q` on `X`, if all cohomology of `Q` on every
fibre of `f` over a rational point of an open `U` of `Y` vanishes, then every higher direct
image `Rⁿ f_* Q` restricts to zero on `U`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

section BaseIndependence

variable {X : Scheme.{u}}

/-- `Hⁿ(X, M)` vanishes as a `Γ(X, ⊤)`-module exactly when it vanishes as an `R`-module
for any `f : X ⟶ Spec R`. -/
theorem isZero_cohomology_iff_relativeCohomology {R : CommRingCat.{u}} (f : X ⟶ Spec R)
    (n : ℕ) (M : X.Modules) :
    IsZero ((cohomology X n).obj M) ↔ IsZero ((relativeCohomology f n).obj M) := by
  rw [← ((relativeCohomologyRestrictScalarsIso f n).app M).isZero_iff, Functor.comp_obj,
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

/-- Vanishing of relative cohomology does not depend on the affine base. -/
theorem isZero_relativeCohomology_iff {R₁ R₂ : CommRingCat.{u}} (f₁ : X ⟶ Spec R₁)
    (f₂ : X ⟶ Spec R₂) (n : ℕ) (M : X.Modules) :
    IsZero ((relativeCohomology f₁ n).obj M) ↔ IsZero ((relativeCohomology f₂ n).obj M) :=
  (isZero_cohomology_iff_relativeCohomology f₁ n M).symm.trans
    (isZero_cohomology_iff_relativeCohomology f₂ n M)

end BaseIndependence

section Transport

/-- Vanishing of the cohomology of a pulled-back module is invariant under an isomorphism of
schemes over `X`, for any affine bases. -/
theorem isZero_relativeCohomology_pullback_of_iso {X P₁ P₂ : Scheme.{u}} (E : P₂ ≅ P₁)
    (a : P₁ ⟶ X) {R₁ R₂ : CommRingCat.{u}} (s₁ : P₁ ⟶ Spec R₁) (s₂ : P₂ ⟶ Spec R₂)
    (M : X.Modules) (n : ℕ)
    (h : IsZero ((relativeCohomology s₁ n).obj ((Scheme.Modules.pullback a).obj M))) :
    IsZero ((relativeCohomology s₂ n).obj ((Scheme.Modules.pullback (E.hom ≫ a)).obj M)) := by
  rw [isZero_relativeCohomology_iff s₂ (E.hom ≫ s₁)]
  exact (h.of_iso (relativeCohomologyPullbackIso E s₁ _ n)).of_iso
    ((relativeCohomology (E.hom ≫ s₁) n).mapIso
      ((Scheme.Modules.pullbackComp E.hom a).app M).symm)

/-- Let `P₁` and `P₂` be fibre products of `f : X ⟶ Y` with `y₁ : T₁ ⟶ Y` and `y₂ : T₂ ⟶ Y`,
where `y₂` is `y₁` precomposed with an isomorphism `T₂ ≅ T₁`. If the cohomology of the
pullback of `M` to `P₁` vanishes, so does the cohomology of its pullback to `P₂`, for any
affine bases. -/
theorem isZero_relativeCohomology_of_isPullback {X Y T₁ T₂ P₁ P₂ : Scheme.{u}} (f : X ⟶ Y)
    {a₁ : P₁ ⟶ X} {b₁ : P₁ ⟶ T₁} {y₁ : T₁ ⟶ Y} (h₁ : IsPullback a₁ b₁ f y₁)
    {a₂ : P₂ ⟶ X} {b₂ : P₂ ⟶ T₂} {y₂ : T₂ ⟶ Y} (h₂ : IsPullback a₂ b₂ f y₂)
    (e : T₂ ≅ T₁) (he : e.hom ≫ y₁ = y₂) {R₁ R₂ : CommRingCat.{u}} (s₁ : P₁ ⟶ Spec R₁)
    (s₂ : P₂ ⟶ Spec R₂) (M : X.Modules) (n : ℕ)
    (h : IsZero ((relativeCohomology s₁ n).obj ((Scheme.Modules.pullback a₁).obj M))) :
    IsZero ((relativeCohomology s₂ n).obj ((Scheme.Modules.pullback a₂).obj M)) := by
  have hiso : IsPullback (𝟙 P₂) (b₂ ≫ e.hom) b₂ e.inv :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have h₂' : IsPullback a₂ (b₂ ≫ e.hom) f y₁ := by
    simpa [← he] using hiso.paste_horiz h₂
  rw [← h₂'.isoIsPullback_hom_fst _ _ h₁]
  exact isZero_relativeCohomology_pullback_of_iso _ a₁ s₁ s₂ M n h

end Transport

section AffineRestrict

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)

/-- The restriction `f⁻¹ V ⟶ V ≅ Spec Γ(Y, V)` of `f` over an affine open `V`. -/
def affineRestrict : (f ⁻¹ᵁ V).toScheme ⟶ Spec Γ(Y, V) :=
  f ∣_ V ≫ hV.isoSpec.hom

instance [Smooth f] : Smooth (affineRestrict f hV) := by
  delta affineRestrict; infer_instance

instance [IsProper f] : IsProper (affineRestrict f hV) := by
  delta affineRestrict; infer_instance

/-- `f⁻¹ V` is the fibre product of `f` with `Spec Γ(Y, V) ⟶ Y`. -/
theorem isPullback_affineRestrict :
    IsPullback (f ⁻¹ᵁ V).ι (affineRestrict f hV) f hV.fromSpec := by
  have hiso : IsPullback (𝟙 _) (affineRestrict f hV) (f ∣_ V) hV.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨by simp [affineRestrict]⟩
  simpa [IsAffineOpen.isoSpec_inv_ι] using hiso.paste_horiz (isPullback_morphismRestrict f V).flip

end AffineRestrict

section RationalPoint

variable (K : Type u) [Field K] [IsAlgClosed K] {Y : Scheme.{u}}
  (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g] {V : Y.Opens} (hV : IsAffineOpen V)

/-- **Nullstellensatz.** For a maximal ideal `m` of the sections over an affine open `V` of
a scheme locally of finite type over an algebraically closed field `K`, the closed point
`Spec (Γ(Y, V) ⧸ m) ⟶ Y` becomes a rational point after composing with an isomorphism
`Spec K ≅ Spec (Γ(Y, V) ⧸ m)`. -/
theorem exists_iso_rationalPoint (m : Ideal Γ(Y, V)) [m.IsMaximal] :
    ∃ e : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)),
      e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec ≫ g = 𝟙 _ := by
  let θ : CommRingCat.of K ⟶ CommRingCat.of (Γ(Y, V) ⧸ m) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ V le_top ≫ idealQuotientHom m
  have hft : θ.hom.FiniteType := by
    have h₁ : (g.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType g inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    have h₀ : (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv).2
    have h₂ : (idealQuotientHom m).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective
    exact (h₂.comp h₁).comp h₀
  let := Ideal.Quotient.field m
  have hfin : (θ.hom : K →+* Γ(Y, V) ⧸ m).Finite :=
    (RingHom.finite_iff_finiteType_of_isJacobsonRing (R := K) (S := Γ(Y, V) ⧸ m)).2 hft
  have hbij : Function.Bijective (θ.hom : K →+* Γ(Y, V) ⧸ m) :=
    IsAlgClosed.ringHom_bijective_of_isIntegral (k := K) (K := Γ(Y, V) ⧸ m) θ.hom
      hfin.to_isIntegral
  have : IsIso θ := (ConcreteCategory.isIso_iff_bijective θ).2 hbij
  refine ⟨(asIso (Spec.map θ)).symm, ?_⟩
  have hθ : Spec.map (idealQuotientHom m) ≫ hV.fromSpec ≫ g = Spec.map θ := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV le_top,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
    simp only [θ, Spec.map_comp, Category.assoc]
  rw [hθ]
  simp

/-- The rational point of `exists_iso_rationalPoint`, factored through an open `U ⊇ V`: a
morphism `x : Spec K ⟶ U` with `x ≫ U.ι ≫ g = 𝟙` whose composite with `U.ι` is
`Spec K ≅ Spec (Γ(Y, V) ⧸ m) ⟶ Spec Γ(Y, V) ⟶ Y`. -/
theorem exists_rationalPoint_of_le {U : Y.Opens} (hVU : V ≤ U) (m : Ideal Γ(Y, V))
    [m.IsMaximal] :
    ∃ (e : Spec (CommRingCat.of K) ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)))
      (x : Spec (CommRingCat.of K) ⟶ U.toScheme),
      x ≫ U.ι = e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec ∧
        x ≫ U.ι ≫ g = 𝟙 _ := by
  obtain ⟨e, he⟩ := exists_iso_rationalPoint K g hV m
  let y : Spec (CommRingCat.of K) ⟶ Y := e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec
  have hy : Set.range y ⊆ Set.range U.ι := by
    have h₁ : Set.range y ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨t, rfl⟩
      exact ⟨Spec.map (idealQuotientHom m) (e.hom t), by simp only [y, Scheme.Hom.comp_apply]⟩
    exact h₁.trans (hV.range_fromSpec.trans_subset
      ((SetLike.coe_subset_coe.2 hVU).trans (Scheme.Opens.range_ι U).ge))
  have hx : IsOpenImmersion.lift U.ι y hy ≫ U.ι = y := IsOpenImmersion.lift_fac _ _ _
  refine ⟨e, IsOpenImmersion.lift U.ι y hy, hx, ?_⟩
  rw [← Category.assoc, hx]
  simpa [y] using he

end RationalPoint

section QuotientFibre

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {V : Y.Opens} (hV : IsAffineOpen V)

/-- Let `m` be an ideal of `Γ(Y, V)` for an affine open `V`, and let `y : T ⟶ Y` be
`T ≅ Spec (Γ(Y, V) ⧸ m) ⟶ Spec Γ(Y, V) ⟶ Y`. If the cohomology of the pullback of `M` to the
fibre product `X ×_Y T` vanishes, so does the cohomology of the pullback of `M|_{f⁻¹ V}` to
the fibre of `affineRestrict f hV` over `Spec (Γ(Y, V) ⧸ m)`, as a `Γ(Y, V) ⧸ m`-module. -/
theorem isZero_relativeCohomology_quotientFibre {T : Scheme.{u}} (y : T ⟶ Y)
    (m : Ideal Γ(Y, V)) (e : T ≅ Spec (CommRingCat.of (Γ(Y, V) ⧸ m)))
    (he : e.hom ≫ Spec.map (idealQuotientHom m) ≫ hV.fromSpec = y) (M : X.Modules) (n : ℕ)
    {R : CommRingCat.{u}} (s : pullback f y ⟶ Spec R)
    (h : IsZero ((relativeCohomology s n).obj
      ((Scheme.Modules.pullback (pullback.fst f y)).obj M))) :
    IsZero ((relativeCohomology
        (pullback.snd (affineRestrict f hV) (Spec.map (idealQuotientHom m))) n).obj
      ((Scheme.Modules.pullback
          (pullback.fst (affineRestrict f hV) (Spec.map (idealQuotientHom m)))).obj
        ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj M))) := by
  have hfib := isZero_relativeCohomology_of_isPullback f (IsPullback.of_hasPullback f y)
    ((IsPullback.of_hasPullback (affineRestrict f hV) (Spec.map (idealQuotientHom m))).paste_horiz
      (isPullback_affineRestrict f hV))
    e.symm (by simp [← he]) s
    (pullback.snd (affineRestrict f hV) (Spec.map (idealQuotientHom m))) M n h
  exact hfib.of_iso ((relativeCohomology _ n).mapIso
    ((Scheme.Modules.pullbackComp _ (f ⁻¹ᵁ V).ι).app M))

end QuotientFibre

/-- Assuming `UniversalPerfectSectionsStatement`, let `K` be an algebraically closed field,
`g : Y ⟶ Spec K` locally of finite type, `f : X ⟶ Y` smooth and proper, `Q` a line bundle on
`X` and `U` an open of `Y`. If for every rational point `x` of `U` and every `n` the
cohomology `Hⁿ` of the pullback of `Q` to the fibre `X ×_Y Spec K` over `x` vanishes, then
every higher direct image `Rⁿ f_* Q` restricts to zero on `U`. -/
theorem isZero_pullback_higherDirectImage_of_rationalFibres
    (hups : UniversalPerfectSectionsStatement.{u})
    (K : Type u) [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
    (g : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType g]
    (f : X ⟶ Y) [Smooth f] [IsProper f] (Q : Picard.LineBundle X) (U : Y.Opens)
    (hQ : ∀ x : Spec (CommRingCat.of K) ⟶ U.toScheme,
      x ≫ U.ι ≫ g = 𝟙 (Spec (CommRingCat.of K)) → ∀ n : ℕ,
        IsZero ((relativeCohomology (pullback.snd f (x ≫ U.ι)) n).obj
          ((Scheme.Modules.pullback (pullback.fst f (x ≫ U.ι))).obj Q.obj)))
    (n : ℕ) :
    IsZero ((Scheme.Modules.pullback U.ι).obj ((higherDirectImage f n).obj Q.obj)) := by
  refine isZero_pullback_higherDirectImage_of_affineOpens f U n Q.obj fun V hV hVU => ?_
  let h := affineRestrict f hV
  let L := (Picard.LineBundle.pullback (f ⁻¹ᵁ V).ι).obj Q
  have key : IsZero ((relativeCohomology h n).obj L.obj) := by
    refine isZero_relativeCohomology_of_universalPerfectSections hups h L (fun m hm k => ?_) n
    obtain ⟨e, x, hx, hx'⟩ := exists_rationalPoint_of_le K g hV hVU m
    exact isZero_relativeCohomology_quotientFibre f hV (x ≫ U.ι) m e hx.symm Q.obj k
      (pullback.snd f (x ≫ U.ι)) (hQ x hx' k)
  exact ((isZero_cohomology_iff_relativeCohomology h n _).2 key).of_iso
    ((cohomology _ n).mapIso ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ V).ι).app Q.obj))

end Langlands.AlgebraicGeometry.Modules.DerivedSections
