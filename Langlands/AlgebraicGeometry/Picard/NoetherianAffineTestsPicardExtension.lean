import Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsUniversalElement
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralRigidifiedComparison
import Langlands.AlgebraicGeometry.Picard.AffineStageEnlargement
import Langlands.AlgebraicGeometry.Picard.RelativeSpaceCartesian
import Langlands.AlgebraicGeometry.NoetherianApproximation.LineBundleIsoSubalgebraDescentProof

/-! # The Picard class sheaf is represented once it is represented on noetherian affine tests -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Picard.NoetherianAffineTests

open RelativePicard

/-- Line bundles that are isomorphic have the same fppf Picard class. -/
lemma sheafClassOf_eq_of_iso {S X : Scheme.{u}} (f : X ⟶ S) (T : Over S)
    {L M : LineBundle ((relativeSpace f).obj T)} (e : L ≅ M) :
    sheafClassOf f T L = sheafClassOf f T M :=
  congrArg ((toClassSheaf f).app (op T)) ((classOf_eq_iff_iso f T L M).2 ⟨e⟩)

/-- Pulling a section back along each morphism to `P` is bijective on a test object as soon as
it is bijective on an isomorphic test object. -/
lemma bijective_of_iso {C : Type*} [Category C] {P T T' : C} (e : T ≅ T')
    {F : Cᵒᵖ ⥤ Type*} (ξ : F.obj (op P))
    (h : Function.Bijective (fun g : T ⟶ P ↦ F.map g.op ξ)) :
    Function.Bijective (fun g : T' ⟶ P ↦ F.map g.op ξ) := by
  constructor
  · intro g₁ g₂ hg
    change F.map g₁.op ξ = F.map g₂.op ξ at hg
    have h' : F.map (e.hom ≫ g₁).op ξ = F.map (e.hom ≫ g₂).op ξ := by
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, hg]
    exact (cancel_epi e.hom).1 (h.1 h')
  · intro x
    obtain ⟨g, hg⟩ := h.2 (F.map e.hom.op x)
    refine ⟨e.inv ≫ g, ?_⟩
    change F.map (e.inv ≫ g).op ξ = x
    change F.map g.op ξ = F.map e.hom.op x at hg
    rw [op_comp, Functor.map_comp_apply, hg, ← Functor.map_comp_apply, ← op_comp,
      e.inv_hom_id, op_id, F.map_id, types_id_apply]

section Rigidified

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
  [GeometricallyIntegral f] (ε : S ⟶ X) (hε : ε ≫ f = 𝟙 S)

/-- Every section of the fppf Picard class sheaf is the class of a line bundle underlying a
rigidified line bundle. -/
lemma exists_rigidified_sheafClassOf (T : Over S) (x : (classSheafPresheaf f).obj (op T)) :
    ∃ r : RigidifiedLineBundle.relative f ε hε T,
      sheafClassOf f T ((RigidifiedLineBundle.forget _).obj r) = x := by
  let Θ := RigidifiedLineBundle.properFlatIntegralClassIso f ε hε
  obtain ⟨r, hr⟩ := Quotient.exists_rep (Θ.inv.app (op T) x)
  refine ⟨r, ?_⟩
  change Θ.hom.app (op T) (RigidifiedLineBundle.classOf f ε hε r) = x
  rw [show RigidifiedLineBundle.classOf f ε hε r = Θ.inv.app (op T) x from hr]
  exact types_congr_hom (Θ.inv_hom_id_app (op T)) x

/-- Rigidified line bundles with the same fppf Picard class have isomorphic underlying line
bundles. -/
lemma nonempty_iso_of_sheafClassOf_eq (T : Over S)
    (r₁ r₂ : RigidifiedLineBundle.relative f ε hε T)
    (h : sheafClassOf f T ((RigidifiedLineBundle.forget _).obj r₁) =
      sheafClassOf f T ((RigidifiedLineBundle.forget _).obj r₂)) :
    Nonempty ((RigidifiedLineBundle.forget _).obj r₁ ≅
      (RigidifiedLineBundle.forget _).obj r₂) := by
  let Θ := RigidifiedLineBundle.properFlatIntegralClassIso f ε hε
  have hinj : Function.Injective (Θ.hom.app (op T)) := fun a b hab ↦ by
    have ha := types_congr_hom (Θ.hom_inv_id_app (op T)) a
    have hb := types_congr_hom (Θ.hom_inv_id_app (op T)) b
    rw [types_comp_apply, types_id_apply] at ha hb
    rw [← ha, ← hb, hab]
  obtain ⟨e⟩ := Quotient.exact (@hinj (RigidifiedLineBundle.classOf f ε hε r₁)
    (RigidifiedLineBundle.classOf f ε hε r₂) h)
  exact ⟨(RigidifiedLineBundle.forget _).mapIso e⟩

/-- If the fppf Picard classes of two rigidified line bundles agree after restriction along
`h`, then their pulled-back line bundles are isomorphic. -/
lemma nonempty_pullback_iso_of_map_eq {T U : Over S} (h : T ⟶ U)
    (r₁ r₂ : RigidifiedLineBundle.relative f ε hε U)
    (hx : (classSheafPresheaf f).map h.op
        (sheafClassOf f U ((RigidifiedLineBundle.forget _).obj r₁)) =
      (classSheafPresheaf f).map h.op
        (sheafClassOf f U ((RigidifiedLineBundle.forget _).obj r₂))) :
    Nonempty ((LineBundle.pullback ((relativeSpace f).map h)).obj
        ((RigidifiedLineBundle.forget _).obj r₁) ≅
      (LineBundle.pullback ((relativeSpace f).map h)).obj
        ((RigidifiedLineBundle.forget _).obj r₂)) := by
  rw [map_sheafClassOf, map_sheafClassOf] at hx
  exact nonempty_iso_of_sheafClassOf_eq f ε hε T
    ((RigidifiedLineBundle.relativePullback f ε hε h).obj r₁)
    ((RigidifiedLineBundle.relativePullback f ε hε h).obj r₂) hx

end Rigidified

section Stages

variable {R : Type u} [CommRing R]

/-- An affine scheme over `Spec R` is isomorphic to the affine test of an `R`-algebra. -/
lemma exists_affineBase_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (A : Type u) (_ : CommRing A) (_ : Algebra R A), Nonempty (affineBase R A ≅ T) := by
  let φ := Spec.preimage (T.left.isoSpec.inv ≫ T.hom)
  let : Algebra R Γ(T.left, ⊤) := φ.hom.toAlgebra
  refine ⟨Γ(T.left, ⊤), inferInstance, this, ⟨Over.isoMk T.left.isoSpec.symm ?_⟩⟩
  change T.left.isoSpec.inv ≫ T.hom = Spec.map (CommRingCat.ofHom φ.hom)
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

variable {A : Type u} [CommRing A] [Algebra R A]

/-- The affine test of a finitely generated algebra over a noetherian ring is noetherian. -/
lemma isNoetherian_affineBase [IsNoetherianRing R] {B : Subalgebra R A} (hB : B.FG) :
    IsNoetherian (affineBase R B).left := by
  have := isNoetherianRing_of_fg hB
  change IsNoetherian (Spec (CommRingCat.of B))
  infer_instance

/-- A line bundle on the base change of a quasi-compact quasi-separated scheme to an affine
test descends to the base change to a finitely generated subalgebra. -/
lemma exists_stage_lineBundle {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] (M : LineBundle ((relativeSpace f).obj (affineBase R A))) :
    ∃ B : Subalgebra R A, B.FG ∧ ∃ L : LineBundle ((relativeSpace f).obj (affineBase R B)),
      Nonempty ((LineBundle.pullback ((relativeSpace f).map (affineSubalgebraMap B))).obj L ≅
        M) := by
  obtain ⟨B, hB, -, M₀, hM₀, hdesc⟩ :=
    NoetherianApproximation.lineBundleSubalgebraDescent f
      (pullback.snd (affineBase R A).hom f) (pullback.fst (affineBase R A).hom f)
      (IsPullback.of_hasPullback (affineBase R A).hom f).flip M.obj M.property ∅
  let q := affineSubalgebraMap B
  let eB := relativeSpaceSymmetry f (affineBase R B)
  let c := (relativeSpace f).map q ≫ eB.hom
  have hc₁ : c ≫ pullback.fst f (affineBase R B).hom =
      pullback.snd (affineBase R A).hom f := by
    dsimp only [c, eB, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst, relativeSpace_map_snd]
  have hc₂ : c ≫ pullback.snd f (affineBase R B).hom =
      pullback.fst (affineBase R A).hom f ≫
        Spec.map (CommRingCat.ofHom (algebraMap B A)) := by
    dsimp only [c, eB, relativeSpaceSymmetry]
    rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
    exact (relativeProjection f).naturality q
  obtain ⟨e⟩ := hdesc c hc₁ hc₂
  refine ⟨B, hB, ⟨(Scheme.Modules.pullback eB.hom).obj M₀, hM₀.pullback eB.hom⟩,
    ⟨ObjectProperty.isoMk _ ?_⟩⟩
  exact (Scheme.Modules.pullbackComp ((relativeSpace f).map q) eB.hom).app M₀ ≪≫ e

/-- Two line bundles on the base change to a finitely generated subalgebra `B` which become
isomorphic over the whole algebra are already isomorphic over a finitely generated subalgebra
containing `B`. -/
lemma exists_stage_pullback_iso {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [QuasiCompact f] [QuasiSeparated f] {B : Subalgebra R A} (hB : B.FG)
    (L₁ L₂ : LineBundle ((relativeSpace f).obj (affineBase R B)))
    (h : Nonempty ((LineBundle.pullback ((relativeSpace f).map (affineSubalgebraMap B))).obj L₁ ≅
      (LineBundle.pullback ((relativeSpace f).map (affineSubalgebraMap B))).obj L₂)) :
    ∃ (C : Subalgebra R A) (hBC : B ≤ C), C.FG ∧
      Nonempty ((LineBundle.pullback ((relativeSpace f).map (affineAlgebraStageMap hBC))).obj
          L₁ ≅
        (LineBundle.pullback ((relativeSpace f).map (affineAlgebraStageMap hBC))).obj L₂) := by
  obtain ⟨e⟩ := h
  obtain ⟨T', hT', -, hstage⟩ := NoetherianApproximation.lineBundleIsoSubalgebraDescent
    (pullback.fst (affineBase R B).hom f) L₁.obj L₂.obj L₁.property L₂.property
    ((relativeSpace f).map (affineSubalgebraMap B)) (pullback.fst (affineBase R A).hom f)
    (relativeProjection_isPullback f (affineSubalgebraMap B))
    ⟨(LineBundle.forget _).mapIso e⟩ ∅
  obtain ⟨hC, hBC⟩ := Subalgebra.fg_restrictScalars_and_le_of_fg B hB T' hT'
  refine ⟨T'.restrictScalars R, hBC, hC, ?_⟩
  obtain ⟨e'⟩ := hstage ((relativeSpace f).map (affineAlgebraStageMap hBC))
    (pullback.fst (affineBase R (T'.restrictScalars R)).hom f)
    (relativeProjection_isPullback f (affineAlgebraStageMap hBC))
  exact ⟨ObjectProperty.isoMk _ e'⟩

end Stages

section Bijective

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (ε : Spec (CommRingCat.of R) ⟶ X) (hε : ε ≫ f = 𝟙 _)
  {P : Over (Spec (CommRingCat.of R))} [LocallyOfFinitePresentation P.hom]
  (ξ : (classSheafPresheaf f).obj (op P))
  (hξ : ∀ T : Over (Spec (CommRingCat.of R)), IsAffine T.left → IsNoetherian T.left →
    Function.Bijective (fun g : T ⟶ P ↦ (classSheafPresheaf f).map g.op ξ))
include hε hξ

/-- Bijectivity on noetherian affine tests propagates to the affine test of every algebra. -/
lemma bijective_affineBase (A : Type u) [CommRing A] [Algebra R A] :
    Function.Bijective (fun g : affineBase R A ⟶ P ↦ (classSheafPresheaf f).map g.op ξ) := by
  have hstage : ∀ {B : Subalgebra R A}, B.FG → Function.Bijective
      (fun g : affineBase R B ⟶ P ↦ (classSheafPresheaf f).map g.op ξ) := fun hB ↦
    hξ _ (inferInstanceAs (IsAffine (Spec _))) (isNoetherian_affineBase hB)
  constructor
  · intro g₁ g₂ hg
    change (classSheafPresheaf f).map g₁.op ξ = (classSheafPresheaf f).map g₂.op ξ at hg
    obtain ⟨B₁, hB₁, -, p₁, hp₁⟩ := exists_affinePoint_subalgebra P g₁ ∅
    obtain ⟨B₂, hB₂, -, p₂, hp₂⟩ := exists_affinePoint_subalgebra P g₂ ∅
    obtain ⟨q₁, hq₁⟩ : ∃ q₁ : affineBase R ↥(B₁ ⊔ B₂) ⟶ P,
        affineSubalgebraMap (B₁ ⊔ B₂) ≫ q₁ = g₁ :=
      ⟨affineAlgebraStageMap (le_sup_left : B₁ ≤ B₁ ⊔ B₂) ≫ p₁, by
        rw [affineAlgebraStageMap_restrict_assoc, hp₁]⟩
    obtain ⟨q₂, hq₂⟩ : ∃ q₂ : affineBase R ↥(B₁ ⊔ B₂) ⟶ P,
        affineSubalgebraMap (B₁ ⊔ B₂) ≫ q₂ = g₂ :=
      ⟨affineAlgebraStageMap (le_sup_right : B₂ ≤ B₁ ⊔ B₂) ≫ p₂, by
        rw [affineAlgebraStageMap_restrict_assoc, hp₂]⟩
    obtain ⟨r₁, hr₁⟩ := exists_rigidified_sheafClassOf f ε hε (affineBase R ↥(B₁ ⊔ B₂))
      ((classSheafPresheaf f).map q₁.op ξ)
    obtain ⟨r₂, hr₂⟩ := exists_rigidified_sheafClassOf f ε hε (affineBase R ↥(B₁ ⊔ B₂))
      ((classSheafPresheaf f).map q₂.op ξ)
    have hx : (classSheafPresheaf f).map (affineSubalgebraMap (B₁ ⊔ B₂)).op
          (sheafClassOf f _ ((RigidifiedLineBundle.forget _).obj r₁)) =
        (classSheafPresheaf f).map (affineSubalgebraMap (B₁ ⊔ B₂)).op
          (sheafClassOf f _ ((RigidifiedLineBundle.forget _).obj r₂)) := by
      rw [hr₁, hr₂, ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
        hq₁, hq₂]
      exact hg
    obtain ⟨C, hBC, hC, ⟨e⟩⟩ := exists_stage_pullback_iso f (hB₁.sup hB₂) _ _
      (nonempty_pullback_iso_of_map_eq f ε hε _ r₁ r₂ hx)
    have hC' : affineAlgebraStageMap hBC ≫ q₁ = affineAlgebraStageMap hBC ≫ q₂ := by
      apply (hstage hC).1
      change (classSheafPresheaf f).map (affineAlgebraStageMap hBC ≫ q₁).op ξ =
        (classSheafPresheaf f).map (affineAlgebraStageMap hBC ≫ q₂).op ξ
      rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ← hr₁, ← hr₂,
        map_sheafClassOf, map_sheafClassOf]
      exact sheafClassOf_eq_of_iso f _ e
    rw [← hq₁, ← hq₂, ← affineAlgebraStageMap_restrict hBC, Category.assoc, Category.assoc, hC']
  · intro x
    obtain ⟨r, hr⟩ := exists_rigidified_sheafClassOf f ε hε _ x
    obtain ⟨B, hB, L, ⟨e⟩⟩ := exists_stage_lineBundle f ((RigidifiedLineBundle.forget _).obj r)
    obtain ⟨p, hp⟩ := (hstage hB).2 (sheafClassOf f _ L)
    refine ⟨affineSubalgebraMap B ≫ p, ?_⟩
    change (classSheafPresheaf f).map p.op ξ = sheafClassOf f _ L at hp
    change (classSheafPresheaf f).map (affineSubalgebraMap B ≫ p).op ξ = x
    rw [op_comp, Functor.map_comp_apply, hp, map_sheafClassOf, ← hr]
    exact sheafClassOf_eq_of_iso f _ e

/-- Bijectivity on noetherian affine tests propagates to every affine test. -/
lemma bijective_of_isAffine (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    Function.Bijective (fun g : T ⟶ P ↦ (classSheafPresheaf f).map g.op ξ) := by
  obtain ⟨A, _, _, ⟨e⟩⟩ := exists_affineBase_iso T
  exact bijective_of_iso e ξ (bijective_affineBase f ε hε ξ hξ A)

end Bijective

/-- **Extension from noetherian affine tests.** Let `f : X ⟶ Spec R` be proper, flat, with
geometrically integral fibres and a section, over a noetherian ring `R`. If a scheme `P` locally
of finite presentation over `Spec R` represents the fppf Picard class sheaf of `f` on the affine
noetherian schemes over `Spec R`, naturally in those tests, then it represents the sheaf on all
schemes over `Spec R`. -/
theorem nonempty_representableBy_of_noetherianAffine {R : Type u} [CommRing R]
    [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    [Flat f] [GeometricallyIntegral f] (ε : Spec (CommRingCat.of R) ⟶ X) (hε : ε ≫ f = 𝟙 _)
    {P : Over (Spec (CommRingCat.of R))} [LocallyOfFinitePresentation P.hom]
    (α : (ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) ↦
          IsAffine T.left ∧ IsNoetherian T.left)).op ⋙ yoneda.obj P ⋙ uliftFunctor.{u + 1} ≅
      (ObjectProperty.ι (fun T : Over (Spec (CommRingCat.of R)) ↦
          IsAffine T.left ∧ IsNoetherian T.left)).op ⋙ classSheafPresheaf f) :
    Nonempty ((classSheafPresheaf f).RepresentableBy P) := by
  have : IsLocallyNoetherian P.left := LocallyOfFiniteType.isLocallyNoetherian P.hom
  obtain ⟨ξ, hξ⟩ := exists_universal_map (F := classSheaf f) α
  refine ⟨representableByOfBijectiveAffine (classSheaf f) P ξ fun T hT ↦ ?_⟩
  have := hT
  refine bijective_of_isAffine f ε hε ξ (fun T' hA hN ↦ ?_) T
  have := hA
  have := hN
  have hfun : (fun g : T' ⟶ P ↦ (classSheafPresheaf f).map g.op ξ) = aff α T' :=
    funext (hξ T')
  rw [hfun]
  exact ⟨aff_injective α T', fun x ↦ ⟨affInv α T' x, aff_affInv α T' x⟩⟩

end Langlands.AlgebraicGeometry.Picard.NoetherianAffineTests
