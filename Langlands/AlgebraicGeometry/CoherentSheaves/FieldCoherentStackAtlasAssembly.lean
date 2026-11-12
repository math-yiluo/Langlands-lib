import Langlands.AlgebraicGeometry.CoherentSheaves.FieldCoherentStackAtlasStatement
import Langlands.AlgebraicGeometry.CoherentSheaves.FieldCoherentPointSmoothChartStatement
import Langlands.AlgebraicGeometry.CoherentSheaves.PointFiberIsomScheme
import Langlands.AlgebraicGeometry.CoherentSheaves.FieldProperGeometry
import Langlands.AlgebraicGeometry.CoherentSheaves.CoproductChartFamily
import Langlands.AlgebraicGeometry.CoherentSheaves.FiniteTypeFamilyDescent
import Langlands.AlgebraicGeometry.Modules.FinitePresentationEssentiallySmallStatement
import Langlands.AlgebraicGeometry.Stacks.PointFiberCharts
import Langlands.AlgebraicGeometry.Picard.FiniteTypePicardStackAtlasAssembly

/-! # Smooth atlases of the actual coherent-family stack from charts at finite-type points -/

universe u

open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.CoherentSheaves

open Langlands.CategoryTheory

/-- The actual coherent-family stack with its morphism universe lifted. -/
abbrev liftedStack {S X : Scheme.{u}} (f : X ⟶ S) :
    LocallyDiscrete (Over S)ᵒᵖ ⥤ᵖ Cat.{u + 1, u + 1} :=
  PseudofunctorHomLift.homLift.{u + 1} (FamilyGroupoid.pseudofunctor f)

section Representatives

variable {S X : Scheme.{u}} (f : X ⟶ S)

/-- Essential smallness of finitely presented modules gives a family of
representatives, indexed by a type in `Type u`, of all actual families on a test. -/
lemma exists_family_representatives
    (hS : Modules.FinitePresentationEssentiallySmallStatement.{u}) (T : Over S) :
    ∃ (ι : Type u) (N : ι → FamilyGroupoid f T),
      ∀ M : FamilyGroupoid f T, ∃ i, Nonempty (N i ≅ M) := by
  let Y := (Picard.relativeSpace f).obj T
  let p := (Picard.relativeProjection f).app T
  have := hS Y
  obtain ⟨Q, hQ, hle⟩ := ObjectProperty.EssentiallySmall.exists_small_le'.{u}
    (SheafOfModules.isFinitePresentation.{u} Y.ringCatSheaf)
  have : Small.{u} (Subtype Q) := hQ
  let ι := {x : Shrink.{u} (Subtype Q) // IsFamily p ((equivShrink (Subtype Q)).symm x).1}
  refine ⟨ι, fun i ↦ ⟨⟨((equivShrink _).symm i.1).1, i.2⟩⟩, fun M ↦ ?_⟩
  obtain ⟨Y', hY', ⟨e⟩⟩ := hle _ M.of.property.1
  let x := equivShrink (Subtype Q) ⟨Y', hY'⟩
  have hx : ((equivShrink (Subtype Q)).symm x).1 = Y' := by simp [x]
  refine ⟨⟨x, ?_⟩, ⟨Core.isoMk (ObjectProperty.isoMk _ ?_)⟩⟩
  · rw [hx]
    exact M.of.property.of_iso e
  · exact eqToIso hx ≪≫ e.symm

end Representatives

section Representability

variable {S X : Scheme.{u}} (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]

/-- The proper Isom theorem represents every actual point fibre by a scheme. -/
lemma exists_pointFiber_representation (hI : ProperIsomRepresentabilityStatement.{u})
    {U T : Over S} (ξ : (liftedStack f).obj (.mk (op U)))
    (η : (liftedStack f).obj (.mk (op T))) :
    ∃ P : Over T.left,
      Nonempty ((AlgebraicSpace.schemeYoneda T.left).obj P ≅
        Stacks.pointFiberPresheaf (liftedStack f) ξ η) := by
  obtain ⟨I, e, -, -⟩ := FamilyGroupoid.exists_pointFiberIsomScheme_of_properIsom f
    (ULiftHom.objDown.{u + 1, u + 1} ξ) (ULiftHom.objDown.{u + 1, u + 1} η) hI
    inferInstance inferInstance
  exact ⟨_, e⟩

end Representability

section Coproduct

open AlgebraicSpace.CoproductChart

variable {S X : Scheme.{u}} (f : X ⟶ S) {ι : Type u} (V : ι → Over S)
  (M : ∀ i, FamilyGroupoid f (V i))

/-- Every representing scheme of a point fibre of the glued coproduct family is
smooth when the component families have smooth point fibres. -/
lemma smooth_of_coproductFamily
    (hsm : ∀ i, Stacks.HasSmoothPointFibers (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} (M i)))
    {T : Over S} (η : (liftedStack f).obj (.mk (op T))) {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅
      Stacks.pointFiberPresheaf (liftedStack f)
        (ULiftHom.objUp.{u + 1, u + 1} (CoproductChartFamily.family f V M)) η) :
    Smooth P.hom :=
  Stacks.smooth_of_coproductChart V _ (fun i ↦ ULiftHom.objUp.{u + 1, u + 1} (M i))
    (fun i ↦ (ULiftHom.up : FamilyGroupoid f (V i) ⥤ ULiftHom.{u + 1} (FamilyGroupoid f (V i))).mapIso
      (CoproductChartFamily.familyIso f V M i)) η (fun i ↦ hsm i T η) e

end Coproduct

section ChartPoints

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A chart point whose pulled-back chart family is the pulled-back test family
lies over a point in the image of every representing scheme. -/
lemma mem_range_of_familyChartPoint {U : Over (Spec (CommRingCat.of k))}
    (ξ : FamilyGroupoid f U) {B : Type u} [CommRing B] [Algebra k B]
    (M₀ : FamilyGroupoid f (Picard.affineBase k B))
    {Q : Over (Picard.affineBase k B).left}
    (e : (AlgebraicSpace.schemeYoneda (Picard.affineBase k B).left).obj Q ≅
      Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
        (ULiftHom.objUp.{u + 1, u + 1} M₀))
    {K : Type u} [Field K] [Algebra k K] (ψ : B →ₐ[k] K)
    (a : Picard.affineBase k K ⟶ U)
    (c : (FamilyGroupoid.pullback f a).obj ξ ≅
      (FamilyGroupoid.pullback f (Picard.affineBaseMap ψ)).obj M₀)
    (x : (Spec (CommRingCat.of K) : Scheme.{u})) :
    (Picard.affineBaseMap ψ).left.base x ∈ Set.range Q.hom.base :=
  Stacks.mem_range_of_chartPoint e (Picard.affineBaseMap ψ) a
    ((ULiftHom.up : FamilyGroupoid f _ ⥤ ULiftHom.{u + 1} (FamilyGroupoid f _)).mapIso c) x

end ChartPoints

section Surjectivity

open Picard.PicardGroupoid

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- Over a finite-type affine test, a smooth representing scheme is surjective
when every family at every presented field point is a pulled-back chart family. -/
lemma surjective_of_chartPoints {U : Over (Spec (CommRingCat.of k))} (ξ : FamilyGroupoid f U)
    (hpt : ∀ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) k))
      (N : FamilyGroupoid f (Picard.affineBase k (PointField n m))),
      ∃ a : Picard.affineBase k (PointField n m) ⟶ U,
        Nonempty ((FamilyGroupoid.pullback f a).obj ξ ≅ N))
    {B : Type u} [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
    (M₀ : FamilyGroupoid f (Picard.affineBase k B)) {Q : Over (Picard.affineBase k B).left}
    (e : (AlgebraicSpace.schemeYoneda (Picard.affineBase k B).left).obj Q ≅
      Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
        (ULiftHom.objUp.{u + 1, u + 1} M₀))
    (hQ : Smooth Q.hom) : Surjective Q.hom := by
  have : IsJacobsonRing B := isJacobsonRing_of_finiteType (A := k)
  have : JacobsonSpace (Picard.affineBase k B).left :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of B)))
  refine surjective_of_isOpenMap_of_closedPoints Q.hom Q.hom.isOpenMap (fun y hy ↦ ?_)
  have hy' : (y : PrimeSpectrum B).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal (y : PrimeSpectrum B)).mp hy
  obtain ⟨n, m, ψ, hψ⟩ := exists_pointField_base_eq (y : PrimeSpectrum B) hy'
  obtain ⟨a, ⟨c⟩⟩ := hpt n m ((FamilyGroupoid.pullback f (Picard.affineBaseMap ψ)).obj M₀)
  let x : (Spec (CommRingCat.of (PointField n m)) : Scheme.{u}) :=
    (⊥ : PrimeSpectrum (PointField n m))
  rw [← hψ x]
  exact mem_range_of_familyChartPoint f ξ M₀ e ψ a c x

/-- A representing scheme over an arbitrary test is surjective when all point
fibres over finite-type affine tests have surjective representing schemes. The
proof descends the test family at each residue field to a finite-type test. -/
lemma surjective_of_finiteTypeTests [QuasiCompact f] [IsSeparated f] [LocallyOfFiniteType f]
    {U : Over (Spec (CommRingCat.of k))} (ξ : FamilyGroupoid f U)
    (hft : ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (M₀ : FamilyGroupoid f (Picard.affineBase k B)),
      ∃ Q : Over (Picard.affineBase k B).left,
        Nonempty ((AlgebraicSpace.schemeYoneda (Picard.affineBase k B).left).obj Q ≅
          Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
            (ULiftHom.objUp.{u + 1, u + 1} M₀)) ∧ Surjective Q.hom)
    {T : Over (Spec (CommRingCat.of k))} (η : FamilyGroupoid f T) {P : Over T.left}
    (e : (AlgebraicSpace.schemeYoneda T.left).obj P ≅
      Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
        (ULiftHom.objUp.{u + 1, u + 1} η)) : Surjective P.hom := by
  refine ⟨fun t ↦ ?_⟩
  let ψ : CommRingCat.of k ⟶ T.left.residueField t :=
    Spec.preimage (T.left.fromSpecResidueField t ≫ T.hom)
  let : Algebra k (T.left.residueField t) := ψ.hom.toAlgebra
  have hw : T.left.fromSpecResidueField t ≫ T.hom =
      (Picard.affineBase k (T.left.residueField t)).hom := by
    change _ = Spec.map (CommRingCat.ofHom ψ.hom)
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  let g : Picard.affineBase k (T.left.residueField t) ⟶ T :=
    Over.homMk (T.left.fromSpecResidueField t) hw
  obtain ⟨B, _, _, _, φ, M₀, ⟨eM⟩⟩ :=
    FamilyDescent.exists_finiteType_model f ((FamilyGroupoid.pullback f g).obj η)
  obtain ⟨Q, ⟨eQ⟩, hQ⟩ := hft B M₀
  let e₁ := Stacks.pullbackRepresentationIso (F := liftedStack f)
    (ULiftHom.objUp.{u + 1, u + 1} ξ) (Picard.affineBaseMap φ) eQ
  let e₂ : Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
      (ULiftHom.objUp.{u + 1, u + 1}
        ((FamilyGroupoid.pullback f (Picard.affineBaseMap φ)).obj M₀)) ≅
      Stacks.pointFiberPresheaf (liftedStack f) (ULiftHom.objUp.{u + 1, u + 1} ξ)
        (ULiftHom.objUp.{u + 1, u + 1} ((FamilyGroupoid.pullback f g).obj η)) :=
    Stacks.pointFiberPresheafIsoOfTestIso (F := liftedStack f)
      (ULiftHom.objUp.{u + 1, u + 1} ξ)
      ((ULiftHom.up : FamilyGroupoid f _ ⥤ ULiftHom.{u + 1} (FamilyGroupoid f _)).mapIso eM)
  let eQ' := e₁ ≪≫ e₂
  let eP' := Stacks.pullbackRepresentationIso (F := liftedStack f)
    (ULiftHom.objUp.{u + 1, u + 1} ξ) g e
  let i := Picard.PicardGroupoid.representingIso eQ' eP'
  have hsQ : Surjective ((Over.pullback (Picard.affineBaseMap φ).left).obj Q).hom := by
    change Surjective (pullback.snd Q.hom (Picard.affineBaseMap φ).left)
    infer_instance
  have hsP : Surjective ((Over.pullback g.left).obj P).hom := by
    rw [← Over.w i.inv]
    infer_instance
  obtain ⟨z, hz⟩ := hsP.surj (IsLocalRing.closedPoint (T.left.residueField t))
  refine ⟨(pullback.fst P.hom g.left).base z, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  change g.left.base (((Over.pullback g.left).obj P).hom.base z) = t
  rw [hz]
  exact Scheme.fromSpecResidueField_apply t _

end Surjectivity

open Picard.PicardGroupoid AlgebraicSpace.CoproductChart in
/-- The proper Isom representation theorem, smooth charts through finite-type field
points, and essential smallness of finitely presented modules give a smooth
surjective scheme atlas, locally of finite type over the field, of the actual
coherent-family stack of every proper scheme over every field. -/
theorem fieldCoherentStackAtlas_of_inputs
    (hI : ProperIsomRepresentabilityStatement.{u})
    (hC : FieldCoherentPointSmoothChartStatement.{u})
    (hS : Modules.FinitePresentationEssentiallySmallStatement.{u}) :
    FieldCoherentStackAtlasStatement.{u} := by
  intro k _ X hX
  have : IsProper X.hom := hX
  have : LocallyOfFinitePresentation X.hom := locallyOfFinitePresentation_over_field k X
  -- Representatives of all families at every presented finite-type field point.
  choose ι Nrep hNrep using fun j : Σ n : ℕ, MaximalSpectrum (MvPolynomial (Fin n) k) ↦
    exists_family_representatives X.hom hS (Picard.affineBase k (PointField j.1 j.2))
  -- One smooth chart through each of them.
  choose V M p hV hsm hp using fun i : Σ j, ι j ↦
    hC k X hX (PointField i.1.1 i.1.2) (Nrep i.1 i.2)
  have : ∀ i, LocallyOfFiniteType (V i).hom := hV
  let ξ := CoproductChartFamily.family X.hom V M
  have hsmooth : ∀ {T : Over (Spec (CommRingCat.of k))} (η : (liftedStack X.hom).obj (.mk (op T)))
      {P : Over T.left} (_ : (AlgebraicSpace.schemeYoneda T.left).obj P ≅
        Stacks.pointFiberPresheaf (liftedStack X.hom) (ULiftHom.objUp.{u + 1, u + 1} ξ) η),
      Smooth P.hom := fun η _ e ↦ smooth_of_coproductFamily X.hom V M hsm η e
  have hpt : ∀ (n : ℕ) (m : MaximalSpectrum (MvPolynomial (Fin n) k))
      (N : FamilyGroupoid X.hom (Picard.affineBase k (PointField n m))),
      ∃ a : Picard.affineBase k (PointField n m) ⟶ sigmaOver V,
        Nonempty ((FamilyGroupoid.pullback X.hom a).obj ξ ≅ N) := by
    intro n m N
    obtain ⟨r, ⟨er⟩⟩ := hNrep ⟨n, m⟩ N
    let i : Σ j, ι j := ⟨⟨n, m⟩, r⟩
    refine ⟨p i ≫ sigmaOverι V i, ⟨?_⟩⟩
    exact ((FamilyGroupoid.pullbackComp X.hom (p i) (sigmaOverι V i)).app ξ).symm ≪≫
      (FamilyGroupoid.pullback X.hom (p i)).mapIso
        (CoproductChartFamily.familyIso X.hom V M i) ≪≫ (hp i).some ≪≫ er
  have hft : ∀ (B : Type u) [CommRing B] [Algebra k B] [Algebra.FiniteType k B]
      (M₀ : FamilyGroupoid X.hom (Picard.affineBase k B)),
      ∃ Q : Over (Picard.affineBase k B).left,
        Nonempty ((AlgebraicSpace.schemeYoneda (Picard.affineBase k B).left).obj Q ≅
          Stacks.pointFiberPresheaf (liftedStack X.hom) (ULiftHom.objUp.{u + 1, u + 1} ξ)
            (ULiftHom.objUp.{u + 1, u + 1} M₀)) ∧ Surjective Q.hom := by
    intro B _ _ _ M₀
    obtain ⟨Q, ⟨e⟩⟩ := exists_pointFiber_representation X.hom hI
      (ULiftHom.objUp.{u + 1, u + 1} ξ) (ULiftHom.objUp.{u + 1, u + 1} M₀)
    exact ⟨Q, ⟨e⟩, surjective_of_chartPoints X.hom ξ hpt M₀ e (hsmooth _ e)⟩
  refine ⟨sigmaOver V, ULiftHom.objUp.{u + 1, u + 1} ξ, inferInstance, fun T η ↦ ?_⟩
  obtain ⟨P, ⟨e⟩⟩ := exists_pointFiber_representation X.hom hI
    (ULiftHom.objUp.{u + 1, u + 1} ξ) η
  exact ⟨P, ⟨e⟩, hsmooth η e,
    surjective_of_finiteTypeTests X.hom ξ hft (ULiftHom.objDown.{u + 1, u + 1} η) e⟩

end Langlands.AlgebraicGeometry.CoherentSheaves
