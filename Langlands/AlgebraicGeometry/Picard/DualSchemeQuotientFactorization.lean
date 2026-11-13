import Langlands.AlgebraicGeometry.Picard.DualSchemeSubalgebraFactorization
import Langlands.AlgebraicGeometry.QuotientFactorizationFinitePresentation
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleQuotientDescent

/-! # Morphisms from affine schemes to the chosen dual factor through finitely presented quotients

Every morphism over `Spec R` from `Spec (D ⧸ I)` to the chosen dual of an abelian scheme over
`Spec R` factors through `Spec (D ⧸ J)` for a finitely generated ideal `J ≤ I`. Together with local
finite type, this makes the chosen dual locally of finite presentation over every affine base.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- Let `f : X ⟶ Spec R` be quasi-compact and quasi-separated. A line bundle on
`X ×_R Spec (D ⧸ I)` is isomorphic to the pullback of a line bundle on `X ×_R Spec (D ⧸ J)`, for
some finitely generated ideal `J ≤ I`, along the map induced by `D ⧸ J → D ⧸ I`. -/
theorem exists_lineBundle_quotient {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [QuasiCompact f] [QuasiSeparated f]
    {D : Type u} [CommRing D] [Algebra R D] (I : Ideal D)
    (M : LineBundle ((relativeSpace f).obj (affineBase R (D ⧸ I)))) :
    ∃ (J : Ideal D) (_ : J.FG) (hJ : J ≤ I)
      (L : LineBundle ((relativeSpace f).obj (affineBase R (D ⧸ J)))),
      Nonempty ((LineBundle.pullback ((relativeSpace f).map (affineQuotientMap hJ))).obj L ≅
        M) := by
  obtain ⟨J, hJfg, hJ, M₀, hM₀, hdesc⟩ :=
    NoetherianApproximation.exists_lineBundle_quotient_descent I f
      (pullback.snd (affineBase R (D ⧸ I)).hom f) (pullback.fst (affineBase R (D ⧸ I)).hom f)
      (IsPullback.of_hasPullback (affineBase R (D ⧸ I)).hom f).flip M.obj M.property
  let q : affineBase R (D ⧸ I) ⟶ affineBase R (D ⧸ J) := affineQuotientMap hJ
  let eJ := relativeSpaceSymmetry f (affineBase R (D ⧸ J))
  let c := (relativeSpace f).map q ≫ eJ.hom
  have hc₁ : c ≫ pullback.fst f (affineBase R (D ⧸ J)).hom =
      pullback.snd (affineBase R (D ⧸ I)).hom f := by
    dsimp only [c, eJ, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, relativeSpace_map_snd]
  have hc₂ : c ≫ pullback.snd f (affineBase R (D ⧸ J)).hom =
      pullback.fst (affineBase R (D ⧸ I)).hom f ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ)) := by
    dsimp only [c, eJ, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact (relativeProjection f).naturality q
  obtain ⟨e⟩ := hdesc c hc₁ hc₂
  let L : LineBundle ((relativeSpace f).obj (affineBase R (D ⧸ J))) :=
    ⟨(Scheme.Modules.pullback eJ.hom).obj M₀, hM₀.pullback eJ.hom⟩
  exact ⟨J, hJfg, hJ, L, ⟨ObjectProperty.isoMk _
    ((Scheme.Modules.pullbackComp ((relativeSpace f).map q) eJ.hom).app M₀ ≪≫ e)⟩⟩

/-- Let `q : T ⟶ T₁` be a morphism over `S` and `F` a rigidified family of the abelian scheme `A`
over `T`. If the underlying line bundle of `F` is isomorphic to the pullback along `q` of a line
bundle on `X ×_S T₁`, then the class of `F` is the pullback along `q` of the class of a rigidified
family over `T₁`. -/
theorem exists_rigidifiedFamily_of_lineBundle {S : Scheme.{u}} (A : AbelianScheme S)
    {T T₁ : Over S} (q : T ⟶ T₁) (F : RigidifiedFamily A T)
    (L₁ : LineBundle ((relativeSpace A.X.hom).obj T₁))
    (e : (LineBundle.pullback ((relativeSpace A.X.hom).map q)).obj L₁ ≅
      (RigidifiedLineBundle.forget _).obj F) :
    ∃ F₁ : RigidifiedFamily A T₁,
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A) q
          (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F₁) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F := by
  let f := A.X.hom
  let L₀ : LineBundle ((relativeSpace f).obj T) := (RigidifiedLineBundle.forget _).obj F
  let c : (relativeSpace f).obj T ⟶ (relativeSpace f).obj T₁ := (relativeSpace f).map q
  let ε := (relativeSection f (unitSection A) (unitSection_comp A)).app T
  let ε₁ := (relativeSection f (unitSection A) (unitSection_comp A)).app T₁
  let p := (relativeProjection f).app T
  let p₁ := (relativeProjection f).app T₁
  have sec₁ : ε₁ ≫ p₁ = 𝟙 T₁.left := relativeSection_projection _ _ _ T₁
  have hεc : ε ≫ c = q.left ≫ ε₁ :=
    ((relativeSection f (unitSection A) (unitSection_comp A)).naturality q).symm
  have hcp : c ≫ p₁ = p ≫ q.left := (relativeProjection f).naturality q
  let N₁ : LineBundle T₁.left := (LineBundle.pullback ε₁).obj L₁
  let F₁ : RigidifiedFamily A T₁ :=
    LineBundle.normalize pullbackTensorComparisonIsIso p₁ ε₁ sec₁ L₁ N₁.inverse
      N₁.tensorInverseIso
  refine ⟨F₁, ?_⟩
  -- the carrier of the pulled-back normalized family has the class of `L₀`
  have he : ((LineBundle.pullback c).obj L₁).classOf = L₀.classOf :=
    (LineBundle.classOf_eq_iff_iso _ _).mpr ⟨e⟩
  have hrig : ((LineBundle.pullback ε).obj L₀).classOf = 0 := by
    rw [← LineBundle.classOf_trivial]
    exact (LineBundle.classOf_eq_iff _ _).mpr ⟨F.obj.rigidification.symm⟩
  have hclass : ((LineBundle.pullback c).obj
      ((RigidifiedLineBundle.forget _).obj F₁)).classOf = L₀.classOf := by
    change ((LineBundle.pullback c).obj (LineBundle.tensor pullbackTensorComparisonIsIso L₁
      ((LineBundle.pullback p₁).obj N₁.inverse))).classOf = L₀.classOf
    rw [← Group.pullback_lineBundle_classOf, LineBundle.classOf_tensor, map_add,
      ← Group.pullback_lineBundle_classOf, LineBundle.classOf_inverse,
      ← Group.pullback_lineBundle_classOf, Group.pullback_lineBundle_classOf c L₁, he,
      ← AddMonoidHom.comp_apply, ← Group.pullback_comp, hcp, map_neg,
      Group.pullback_comp, AddMonoidHom.comp_apply,
      ← AddMonoidHom.comp_apply (Group.pullback q.left),
      ← Group.pullback_comp, ← hεc, Group.pullback_comp, AddMonoidHom.comp_apply,
      Group.pullback_lineBundle_classOf c L₁, he, Group.pullback_lineBundle_classOf, hrig,
      map_zero, neg_zero, add_zero]
  obtain ⟨e₁⟩ := (LineBundle.classOf_eq_iff_iso _ _).mp hclass
  exact Quotient.sound (RigidifiedLineBundle.nonempty_iso_of_forget_iso
    pullbackTensorComparisonIsIso p (relativeSection_projection _ _ _ T) e₁)

variable {R : Type u} [CommRing R] (A : AbelianScheme (Spec (CommRingCat.of R)))

/-- A rigidified family over `Spec (D ⧸ I)` is, up to isomorphism, the pullback of a rigidified
family over `Spec (D ⧸ J)` for a finitely generated ideal `J ≤ I`. -/
theorem exists_rigidifiedFamily_quotient {D : Type u} [CommRing D] [Algebra R D] (I : Ideal D)
    (F : RigidifiedFamily A (affineBase R (D ⧸ I))) :
    ∃ (J : Ideal D) (_ : J.FG) (hJ : J ≤ I) (F₁ : RigidifiedFamily A (affineBase R (D ⧸ J))),
      RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
          (affineQuotientMap hJ)
          (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F₁) =
        RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F := by
  obtain ⟨J, hJfg, hJ, L₁, ⟨e⟩⟩ :=
    exists_lineBundle_quotient A.X.hom I ((RigidifiedLineBundle.forget _).obj F)
  obtain ⟨F₁, hF₁⟩ := exists_rigidifiedFamily_of_lineBundle A (affineQuotientMap hJ) F L₁ e
  exact ⟨J, hJfg, hJ, F₁, hF₁⟩

variable (hA : HasDualScheme A)

/-- Every morphism over `Spec R` from `Spec (D ⧸ I)` to the chosen dual factors through
`Spec (D ⧸ J)` for a finitely generated ideal `J ≤ I`. -/
theorem exists_dualScheme_quotient_factorization (D : Type u) [CommRing D] [Algebra R D]
    (I : Ideal D) (x : affineBase R (D ⧸ I) ⟶ dualScheme A hA) :
    ∃ (J : Ideal D) (_ : J.FG) (hJ : J ≤ I) (y : affineBase R (D ⧸ J) ⟶ dualScheme A hA),
      affineQuotientMap hJ ≫ y = x := by
  let F := (RigidifiedLineBundle.relativePullback A.X.hom (unitSection A) (unitSection_comp A)
    x).obj (poincareFamily A hA)
  have hF : IsPicardZeroFamily A F :=
    picardZeroPullback _ A _ _ x _ (poincareFamily_universal A hA).1
  obtain ⟨J, hJfg, hJ, F₁, hF₁⟩ := exists_rigidifiedFamily_quotient A I F
  obtain ⟨U, hU⟩ := exists_isPicardZeroOpenLocus A (affineBase R (D ⧸ J)) F₁
  have hrange : Set.range (affineQuotientMap (R := R) hJ).left ⊆ U := by
    refine (hU _ (affineQuotientMap hJ)).mp ?_
    change IsPicardZeroClass A (RigidifiedLineBundle.classesPullback A.X.hom (unitSection A)
      (unitSection_comp A) (affineQuotientMap hJ)
      (RigidifiedLineBundle.classOf A.X.hom (unitSection A) (unitSection_comp A) F₁))
    rw [hF₁]
    exact hF
  obtain ⟨J₂, hJ₂, hJJ₂, hJ₂I, hJ₂U⟩ := exists_affineQuotientMap_range_subset hJfg hJ U hrange
  let q₂ := RigidifiedLineBundle.classifyingMap A.X.hom (unitSection A) (unitSection_comp A) F₁
    (affineBase R (D ⧸ J₂)) (affineQuotientMap hJJ₂)
  have hq₂ : IsPicardZeroClass A q₂ := (hU _ _).mpr hJ₂U
  refine ⟨J₂, hJ₂, hJ₂I, dualClassify A hA _ ⟨q₂, hq₂⟩, ?_⟩
  rw [← dualClassify_pullback A Langlands.SchemeModule.RigidifiedModule.pullbackCoherence
    picardZeroPullback hA]
  symm
  apply dualClassify_unique
  change _ = RigidifiedLineBundle.classesPullback A.X.hom (unitSection A) (unitSection_comp A)
    (affineQuotientMap hJ₂I) q₂
  rw [← RigidifiedLineBundle.classifyingMap_comp A.X.hom (unitSection A) (unitSection_comp A)
    Langlands.SchemeModule.RigidifiedModule.pullbackCoherence, affineQuotientMap_comp]
  exact hF₁.symm

/-- The chosen dual of an abelian scheme over an arbitrary affine base is locally of finite
presentation. -/
theorem dualScheme_locallyOfFinitePresentation_affine :
    LocallyOfFinitePresentation (dualScheme A hA).hom := by
  have := dualScheme_locallyOfFiniteType A hA
  exact locallyOfFinitePresentation_of_quotientFactorization _
    (fun D _ _ I x ↦ exists_dualScheme_quotient_factorization A hA D I x)

end Langlands.AbelianScheme
