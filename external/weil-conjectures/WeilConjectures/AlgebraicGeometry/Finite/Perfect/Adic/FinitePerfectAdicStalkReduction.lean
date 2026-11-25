/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicEtaleLevelData
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantModelsReduction
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingDerivedLocalConstancy

/-! # Consecutive algebraic stalk reductions

Source: Stacks Project, Tag 09C6, the balancing isomorphism between consecutive levels.
(blueprint: lem-weil-pbc-finite-perfect-adic-stalk-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Pull a supplied derived constant model to a further scheme. -/
private def finitePerfectAdic_pullback_constant_model
    (Y U W : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (f : U ⟶ Y) (g : W ⟶ U) (h : W ⟶ Y) (hg : g ≫ f = h)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)))
    (E : DerivedCategory (ModuleCat.{t + 1} B))
    (e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) f).mapDerivedCategory.obj K ≅
      (constantSheaf U.smallEtaleTopology (ModuleCat.{t + 1} B)).mapDerivedCategory.obj E) :
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) h).mapDerivedCategory.obj K ≅
      (constantSheaf W.smallEtaleTopology (ModuleCat.{t + 1} B)).mapDerivedCategory.obj E :=
  ((Functor.mapDerivedCategoryNatIso
    (AlgebraicGeometry.Etale.upperStarComp (ModuleCat.{t + 1} B) g f h hg.symm)).app K) ≪≫
    ((Functor.mapDerivedCategoryCompIso _ _).app K).symm ≪≫
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B) g).mapDerivedCategory.mapIso e ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).app E ≪≫
    (Functor.mapDerivedCategoryNatIso
      (upperStarConstantSheafIso (ModuleCat.{t + 1} B) g)).app E

/-- Two already descended quotient levels have the expected algebraic scalar extension.
This only relates the two supplied perfect fibres; it constructs neither etale levels
nor their comparison maps, and has no cover-existence conclusion.

Source: Stacks Project, proetale.tex, lemma-connected-adic-lisse (Tag 09C6), the
sentence asserting L_(n+1) tensor^L (A/I^(n+1)) = L_n; Cohomology on Sites,
lemma-locally-constant-map, and tensor compatibility of geometric inverse image.
(blueprint: lem-weil-pbc-finite-perfect-adic-stalk-reduction).

Proof: finite-ring derived local constancy on the connected nonempty chart identifies
both supplied etale levels locally with their geometric stalks at v. Compose with their
recorded small-universe fibre isomorphisms. The two transport maps give local constant
models of the actual quotients by D'.algebra and D.algebra. Refine these covers by
fibre products and choose a member over v. On it, associativity of derived scalar
extension identifies the actual (n+1)-quotient tensored with A/I^(n+1) with the actual
n-quotient. The coefficient compatibility equations identify its scalar map with the
specified quotient homomorphism. Constant realization commutes with derived scalar
extension, so this yields an isomorphism between the constant realizations of the two
claimed algebraic objects. Apply a geometric stalk on that nonempty member. Tensor
pullback and the constant-stalk isomorphism give the required isomorphism in the lifted
module universe. Exact fully faithful universe lift reflects it in the small derived
category. Only these two levels are involved; no compatible choice of transition maps,
normalization of their adjoint transposes, or simultaneous marking is required. -/
theorem finitePerfectAdic_stalk_reduction
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (V : X.Etale) (hconn : ConnectedSpace V.left) (v : V.left) (n : ℕ)
    (D' : FinitePerfectAdicEtaleLevelData X d φ M V v (n + 1))
    (D : FinitePerfectAdicEtaleLevelData X d φ M V v n) :
    Nonempty
      ((ConstantScalarRealization.moduleDerivedExtension
        (Ideal.Quotient.factorPowSucc d.ideal (n + 1))).obj D'.algebra ≅ D.algebra) := by
  classical
  have : etalePrecoverage.{t}.IsStableUnderComposition :=
    inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderComposition
  have : etalePrecoverage.{t}.IsStableUnderBaseChange :=
    inferInstanceAs (precoverage @AlgebraicGeometry.Etale).IsStableUnderBaseChange
  have : JointlySurjective etalePrecoverage.{t} :=
    inferInstanceAs (JointlySurjective (precoverage @AlgebraicGeometry.Etale))
  have : Finite (A ⧸ d.ideal ^ (n + 1 + 1)) := d.quotientFinite (n + 1)
  have : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  let B' := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))
  let B := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))
  obtain ⟨𝒰, h𝒰⟩ :=
    (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy
      V.left B' D'.level D'.bounded D'.lisse).2.2.2 hconn _ (V.left.algClosurePoint v)
  obtain ⟨𝒱, h𝒱⟩ :=
    (AlgebraicGeometry.Etale.finiteRing_derived_local_constancy
      V.left B D.level D.bounded D.lisse).2.2.2 hconn _ (V.left.algClosurePoint v)
  let 𝒲 : Cover.{t} etalePrecoverage V.left := 𝒰.inter 𝒱
  obtain ⟨i, w, -⟩ := 𝒲.exists_eq v
  let W : X.Etale := Etale.mk (𝒲.f i ≫ V.hom)
  let cU := constantSheaf (𝒰.X i.1).smallEtaleTopology (ModuleCat.{t + 1} B')
  let cV := constantSheaf (𝒱.X i.2).smallEtaleTopology (ModuleCat.{t + 1} B)
  let cW' := constantSheaf (𝒲.X i).smallEtaleTopology (ModuleCat.{t + 1} B')
  let cW := constantSheaf (𝒲.X i).smallEtaleTopology (ModuleCat.{t + 1} B)
  have e' : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B')
        (𝒲.f i)).mapDerivedCategory.obj D'.level ≅
      cW'.mapDerivedCategory.obj ((finitePerfectAdicAlgebraLift _).obj D'.algebra) :=
    finitePerfectAdic_pullback_constant_model V.left (𝒰.X i.1) (𝒲.X i) B'
      (𝒰.f i.1) (pullback.fst (𝒰.f i.1) (𝒱.f i.2)) (𝒲.f i) rfl D'.level _
      ((h𝒰 i.1).some ≪≫ cU.mapDerivedCategory.mapIso D'.stalk.some)
  have e : (AlgebraicGeometry.Etale.upperStar (ModuleCat.{t + 1} B)
        (𝒲.f i)).mapDerivedCategory.obj D.level ≅
      cW.mapDerivedCategory.obj ((finitePerfectAdicAlgebraLift _).obj D.algebra) :=
    finitePerfectAdic_pullback_constant_model V.left (𝒱.X i.2) (𝒲.X i) B
      (𝒱.f i.2) (pullback.snd (𝒰.f i.1) (𝒱.f i.2)) (𝒲.f i)
      pullback.condition.symm D.level _
      ((h𝒱 i.2).some ≪≫ cV.mapDerivedCategory.mapIso D.stalk.some)
  exact finitePerfectAdic_constant_models_reduction X d φ hφ hcompat M n W w
    D'.algebra D.algebra D'.perfect D.perfect
    (D'.transport (𝒲.etalePrecoverageToEtale i) D'.algebra ⟨e'⟩ W (𝟙 W))
    (D.transport (𝒲.etalePrecoverageToEtale i) D.algebra ⟨e⟩ W (𝟙 W))

end AlgebraicGeometry.Scheme
