/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
public import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplex

/-! # Horseshoe total boundary and augmentation naturality

Source: Stacks Project, Tags 01EQ and 0117.
(blueprint: lem-pc-abelian-cech-horseshoe-total-boundary)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

private theorem cechAdditive {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) :
    (TopCat.Sheaf.cechComplexFunctor U).Additive := by
  constructor
  intro A B f g
  apply HomologicalComplex.hom_ext
  intro n
  ext z
  rfl

attribute [local instance] cechAdditive

private noncomputable def totalCechFunctor {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) :
    CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ ⥤
      CochainComplex AddCommGrpCat.{u} ℕ :=
  (TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor _ (.up ℕ) (.up ℕ) (.up ℕ)

private theorem totalCechPreservesZero {X : Scheme.{u}} {ι : Type u}
    (U : ι → X.Opens) : (totalCechFunctor U).PreservesZeroMorphisms := by
  constructor
  intro A B
  change HomologicalComplex₂.total.map _ _ = 0
  rw [show (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
    (((TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ)).map
      (0 : A ⟶ B)) = 0 by
        ext n m z
        rfl, HomologicalComplex₂.total.map_zero]

attribute [local instance] totalCechPreservesZero

set_option backward.isDefEq.respectTransparency false in
private lemma alpha_naturality {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (IA : InjectiveResolution A) (IB : InjectiveResolution B)
    (φ : IA.cocomplex ⟶ IB.cocomplex) :
    abelianCechAlpha U IA ≫ (totalCechFunctor U).map φ =
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℕ)).map φ ≫
          abelianCechAlpha U IB := by
  apply HomologicalComplex.hom_ext
  intro n
  change (TopCat.Sheaf.toCechCochainZero U (IA.cocomplex.X n) ≫
    (abelianCechDouble U IA).ιTotal (.up ℕ) 0 n n _) ≫
      (HomologicalComplex₂.total.map _ _).f n = _
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (TopCat.Sheaf.toCechCochainZero U (IA.cocomplex.X n) ≫
    ((TopCat.Sheaf.cechComplexFunctor U).map (φ.f n)).f 0) ≫
      (abelianCechDouble U IB).ιTotal (.up ℕ) 0 n n _ =
    (φ.f n).hom.app (op (⊤ : X.Opens)) ≫
      TopCat.Sheaf.toCechCochainZero U (IB.cocomplex.X n) ≫
        (abelianCechDouble U IB).ιTotal (.up ℕ) 0 n n _
  rw [← Category.assoc]
  congr 1
  ext z
  funext y
  exact (NatTrans.naturality_apply (φ.f n).hom
    (homOfLE (le_top (a := ⨅ l, U (y l)))).op z)

set_option backward.isDefEq.respectTransparency false in
private lemma beta_naturality {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    {A B : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (IA : InjectiveResolution A) (IB : InjectiveResolution B) (f : A ⟶ B)
    (φ : IA.cocomplex ⟶ IB.cocomplex)
    (hφ : IA.ι ≫ φ = (CochainComplex.single₀ _).map f ≫ IB.ι) :
    abelianCechBeta U IA ≫ (totalCechFunctor U).map φ =
      (TopCat.Sheaf.cechComplexFunctor U).map f ≫ abelianCechBeta U IB := by
  have h₀ : IA.ι.f 0 ≫ φ.f 0 = f ≫ IB.ι.f 0 := by
    simpa using congrArg (fun f ↦ f.f 0) hφ
  apply HomologicalComplex.hom_ext
  intro n
  change (((TopCat.Sheaf.cechComplexFunctor U).map (IA.ι.f 0)).f n ≫
    (abelianCechDouble U IA).ιTotal (.up ℕ) n 0 n _) ≫
      (HomologicalComplex₂.total.map _ _).f n = _
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  change (((TopCat.Sheaf.cechComplexFunctor U).map (IA.ι.f 0)).f n ≫
    ((TopCat.Sheaf.cechComplexFunctor U).map (φ.f 0)).f n) ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, h₀,
    Functor.map_comp, HomologicalComplex.comp_f, Category.assoc]
  rfl

/-- Two maps of short exact sequences have the same target connecting morphism. -/
private theorem boundary_naturality_pair
    {C : Type u} [Category C] [Abelian C]
    {A B V : ShortComplex (CochainComplex C ℕ)}
    (a₁ : A.X₁ ⟶ V.X₁) (a₂ : A.X₂ ⟶ V.X₂) (a₃ : A.X₃ ⟶ V.X₃)
    (b₁ : B.X₁ ⟶ V.X₁) (b₂ : B.X₂ ⟶ V.X₂) (b₃ : B.X₃ ⟶ V.X₃)
    (ha₁ : a₁ ≫ V.f = A.f ≫ a₂) (ha₂ : a₂ ≫ V.g = A.g ≫ a₃)
    (hb₁ : b₁ ≫ V.f = B.f ≫ b₂) (hb₂ : b₂ ≫ V.g = B.g ≫ b₃)
    (hA : A.ShortExact) (hB : B.ShortExact) (hV : V.ShortExact) (q : ℕ) :
    ∃ δ : V.X₃.homology q ⟶ V.X₁.homology (q + 1),
      hA.δ q (q + 1) rfl ≫ HomologicalComplex.homologyMap a₁ (q + 1) =
        HomologicalComplex.homologyMap a₃ q ≫ δ ∧
      hB.δ q (q + 1) rfl ≫ HomologicalComplex.homologyMap b₁ (q + 1) =
        HomologicalComplex.homologyMap b₃ q ≫ δ :=
  ⟨hV.δ q (q + 1) rfl,
    HomologicalComplex.HomologySequence.δ_naturality
      (ShortComplex.homMk a₁ a₂ a₃ ha₁ ha₂) hA hV q (q + 1) rfl,
    HomologicalComplex.HomologySequence.δ_naturality
      (ShortComplex.homMk b₁ b₂ b₃ hb₁ hb₂) hB hV q (q + 1) rfl⟩

/-- Finite-diagonal totalization preserves short exact sequences of double complexes. -/
private theorem total_shortExact_of_shortExact
    (D : ShortComplex (HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ)))
    (hD : D.ShortExact) :
    (ShortComplex.mk (HomologicalComplex₂.total.map D.f (.up ℕ))
      (HomologicalComplex₂.total.map D.g (.up ℕ))
      (by rw [← HomologicalComplex₂.total.map_comp, D.zero,
        HomologicalComplex₂.total.map_zero])).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  let π := ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)
  let J := {i : ℕ × ℕ // π i = n}
  have : Finite J := by
    refine Set.Finite.to_subtype ((Set.finite_Iic (n, n)).subset ?_)
    rintro ⟨p, q⟩ (h : p + q = n)
    simp only [Set.mem_Iic, Prod.mk_le_mk]
    omega
  let E : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ) ⥤
      (Discrete J ⥤ AddCommGrpCat.{u}) :=
    { obj := fun A ↦ Discrete.functor (fun i : J ↦ (A.X i.val.1).X i.val.2)
      map := fun f ↦ Discrete.natTrans (fun i : Discrete J ↦ (f.f i.as.val.1).f i.as.val.2) }
  have : PreservesFiniteLimits E := preservesFiniteLimits_of_evaluation E (fun i ↦ by
    change PreservesFiniteLimits
      (HomologicalComplex.eval _ (.up ℕ) i.as.val.1 ⋙
        HomologicalComplex.eval _ (.up ℕ) i.as.val.2)
    infer_instance)
  have : PreservesFiniteColimits E := preservesFiniteColimits_of_evaluation E (fun i ↦ by
    change PreservesFiniteColimits
      (HomologicalComplex.eval _ (.up ℕ) i.as.val.1 ⋙
        HomologicalComplex.eval _ (.up ℕ) i.as.val.2)
    infer_instance)
  have : E.PreservesZeroMorphisms := by
    constructor
    intro A B
    ext ⟨i⟩
    simp [E]
  let F := E ⋙ colim
  change (D.map F).ShortExact
  exact hD.map_of_exact F

/-- Split resolution rows remain exact after taking Cech cochains and totalizing. -/
private theorem totalCech_shortExact {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (R : ShortComplex
      (CochainComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ℕ))
    (hrows : ∀ n, (R.map (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact)
    (hinj : ∀ n, Injective (R.X₁.X n)) :
    (R.map (totalCechFunctor U)).ShortExact := by
  let G := (TopCat.Sheaf.cechComplexFunctor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)
  have : G.PreservesZeroMorphisms := by
    constructor
    intro A B
    ext n m z
    rfl
  let D := R.map G
  have hD : D.ShortExact := by
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro p
    apply HomologicalComplex.shortExact_of_degreewise_shortExact
    intro n
    have : Injective ((R.map (HomologicalComplex.eval _ (.up ℕ) n)).X₁) :=
      hinj n
    exact (((hrows n).splittingOfInjective.map (TopCat.Sheaf.cechComplexFunctor U)).map
      (HomologicalComplex.eval _ (.up ℕ) p)).shortExact
  exact total_shortExact_of_shortExact D hD

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A prescribed horseshoe gives a common total boundary for alpha and beta.
Source: Stacks 01EQ (the two augmentations) and 0117 (boundary naturality).
(blueprint: lem-pc-abelian-cech-horseshoe-total-boundary)

Proof: Split each resolution row using injectivity of its first term. Apply
sections on every tuple intersection to the splitting equations. Products of
these equations over tuples give split short exact rows of Cech cochains.
Take the direct sums along each finite first-quadrant diagonal: the sums of
row retractions and sections again satisfy the splitting equations. The
cochain maps induced by alpha and beta therefore form a short exact sequence
of total complexes. Define delta to be its homology connecting morphism.
The resolution augmentation equations hα and hβ make the three coefficient
beta maps a morphism from the coefficient Cech short exact sequence to this
total sequence. Tuple surjectivity supplies short exactness of the former.
The three restriction alpha maps give a morphism from the section sequence
specified by hS to the total sequence, since restriction commutes with each
resolution map. Apply HomologySequence.δ_naturality to these two morphisms.
Both use the total differential with Cech degree first, so the signs agree.
Products need no finite index set; only total diagonals are finite. Empty
tuple sets and empty intersections give zero factors and preserve the
splitting equations. Degree zero uses the same connecting-map construction. -/
theorem abelianCechHorseshoe_total_boundary
    {X : Scheme.{u}}
    (T : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))
    (hT : T.ShortExact)
    (I₁ : InjectiveResolution T.X₁) (I₂ : InjectiveResolution T.X₂)
    (I₃ : InjectiveResolution T.X₃)
    (α : I₁.cocomplex ⟶ I₂.cocomplex) (β : I₂.cocomplex ⟶ I₃.cocomplex)
    (hαβ : α ≫ β = 0)
    (hα : I₁.ι ≫ α = (CochainComplex.single₀ _).map T.f ≫ I₂.ι)
    (hβ : I₂.ι ≫ β = (CochainComplex.single₀ _).map T.g ≫ I₃.ι)
    (hrows : ∀ n : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (.up ℕ) n)).ShortExact)
    (hS : ((ShortComplex.mk α β hαβ).map
      ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
        (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℕ))).ShortExact)
    {ι : Type u} (U : ι → X.Opens)
    (hg : ∀ (k : ℕ) (y : Fin (k + 1) → ι),
      Function.Surjective (T.g.hom.app (op (⨅ l, U (y l))))) (q : ℕ) :
    ∃ (δ : ((abelianCechDouble U I₃).total (.up ℕ)).homology q ⟶
        ((abelianCechDouble U I₁).total (.up ℕ)).homology (q + 1)),
      TopCat.Sheaf.cechδ U hT hg q ≫
          HomologicalComplex.homologyMap (abelianCechBeta U I₁) (q + 1) =
        HomologicalComplex.homologyMap (abelianCechBeta U I₃) q ≫ δ ∧
      hS.δ q (q + 1) rfl ≫
          HomologicalComplex.homologyMap (abelianCechAlpha U I₁) (q + 1) =
        HomologicalComplex.homologyMap (abelianCechAlpha U I₃) q ≫ δ  := by
  classical
  let R := ShortComplex.mk α β hαβ
  -- Specify the total objects once, so the augmentation maps have matching endpoints.
  let V := ShortComplex.mk
    (X₁ := (abelianCechDouble U I₁).total (.up ℕ))
    (X₂ := (abelianCechDouble U I₂).total (.up ℕ))
    (X₃ := (abelianCechDouble U I₃).total (.up ℕ))
    ((totalCechFunctor U).map α) ((totalCechFunctor U).map β)
    (by rw [← Functor.map_comp, hαβ, Functor.map_zero])
  have hV : V.ShortExact := totalCech_shortExact U R hrows (fun n ↦ I₁.injective n)
  let A := (ShortComplex.mk α β hαβ).map
    ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj
      (op (⊤ : X.Opens))).mapHomologicalComplex (.up ℕ))
  let C := T.map (TopCat.Sheaf.cechComplexFunctor U)
  have hC : C.ShortExact := TopCat.Sheaf.shortExact_cechComplex hT hg
  exact boundary_naturality_pair (A := C) (B := A) (V := V)
    (abelianCechBeta U I₁) (abelianCechBeta U I₂) (abelianCechBeta U I₃)
    (abelianCechAlpha U I₁) (abelianCechAlpha U I₂) (abelianCechAlpha U I₃)
    (beta_naturality U I₁ I₂ T.f α hα) (beta_naturality U I₂ I₃ T.g β hβ)
    (alpha_naturality U I₁ I₂ α) (alpha_naturality U I₂ I₃ β)
    hC hS hV q

end AlgebraicGeometry.Scheme.Modules
