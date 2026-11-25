/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.RingedInternalHomExactRestriction
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit

/-!
# The finite Koszul system on a ringed site

Source: Stacks Project, More on Algebra, Tag 0913; Cohomology on Sites, Tag 0A0A
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

attribute [local instance 20000] ringedCompletionHasSheafCompose

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u})

/-- Multiplication by a global section on the rank-one module sheaf.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulScalar (s : (O.obj ⋙ forget CommRingCat).sections) :
    End (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
  .of (SheafOfModules.unitHomEquiv _ |>.symm ⟨s.val, s.property⟩)

/-- The positive Koszul factor [O --s^(m+1)--> O] in degrees zero and one.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactor (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedSiteComplex O :=
  HomologicalComplex.double ((ringedKoszulScalar O s ^ (m + 1)).asHom)
    (by decide : (ComplexShape.up ℤ).Rel 0 1)

/-- Components of the forward map (1,s), zero outside degrees zero and one.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactorStepF (s : (O.obj ⋙ forget CommRingCat).sections)
    (m : ℕ) (n : ℤ) :
    (ringedKoszulFactor O s m).X n ⟶ (ringedKoszulFactor O s (m + 1)).X n :=
  if h : n = 0 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₀ _ _).hom ≫
      (HomologicalComplex.doubleXIso₀ _ _).inv ≫
      eqToHom (congrArg (ringedKoszulFactor O s (m + 1)).X h.symm)
  else if h : n = 1 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).hom ≫
      (ringedKoszulScalar O s).asHom ≫
      (HomologicalComplex.doubleXIso₁ _ _ (by decide)).inv ≫
      eqToHom (congrArg (ringedKoszulFactor O s (m + 1)).X h.symm)
  else 0

/-- The components (1,s) commute with the differential.
Proof: the sole nonzero square is s^(m+1) s = s^(m+2); elsewhere both sides vanish.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulFactorStepF_comm
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulFactorStepF O s m n ≫ (ringedKoszulFactor O s (m + 1)).d n k =
      (ringedKoszulFactor O s m).d n k ≫ ringedKoszulFactorStepF O s m k := by
  have hk : n + 1 = k := h
  subst k
  by_cases hn : n = 0
  · subst n
    simp [ringedKoszulFactorStepF, ringedKoszulFactor,
      HomologicalComplex.double_d, pow_succ', End.mul_asHom, Category.assoc]
  · rw [show (ringedKoszulFactor O s (m + 1)).d n (n + 1) = 0 from
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn,
      show (ringedKoszulFactor O s m).d n (n + 1) = 0 from
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn]
    simp

/-- The forward Koszul chain map with components (1,s).
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactorStep (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactor O s m ⟶ ringedKoszulFactor O s (m + 1) where
  f := ringedKoszulFactorStepF O s m
  comm' := ringedKoszulFactorStepF_comm O s m

/-- The total tensor bifunctor of module-sheaf complexes, with its Koszul signs.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensor : ringedSiteComplex O ⥤ ringedSiteComplex O ⥤
    ringedSiteComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  (CategoryTheory.MonoidalCategory.curriedTensor _).map₂HomologicalComplex
    (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)

/-- The strict sequential diagram of the positive one-section Koszul factors.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactors (s : (O.obj ⋙ forget CommRingCat).sections) :
    ℕ ⥤ ringedSiteComplex O :=
  Functor.ofSequence (ringedKoszulFactorStep O s)

/-- The ordered total tensor of the positive Koszul systems.
The empty tensor is the constant diagram O[0]. The index m denotes exponent m+1.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulDiagram : (r : ℕ) →
    (Fin r → (O.obj ⋙ forget CommRingCat).sections) → ℕ ⥤ ringedSiteComplex O :=
  fun r ↦ Nat.rec
    (fun _ ↦ (Functor.const ℕ).obj (ringedSiteRingComplex O))
    (fun _ ih b ↦
      (ringedKoszulFactors O (b 0)).prod' (ih (fun i ↦ b i.succ)) ⋙
        Functor.uncurry.obj (ringedKoszulTensor O)) r

/-- The strict dual inverse tower Hom(P_m,O[0]), including its dual chain maps.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulDualTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ℕᵒᵖ ⥤ ringedSiteComplex O :=
  (ringedKoszulDiagram O r b).op ⋙
    (homComplexFunctor (R := O)).flip.obj (ringedSiteRingComplex O)

/-- Components of the degree-zero projection of a positive Koszul factor.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactorProjectionF (s : (O.obj ⋙ forget CommRingCat).sections)
    (m : ℕ) (n : ℤ) :
    (ringedKoszulFactor O s m).X n ⟶ (ringedSiteRingComplex O).X n :=
  if h : n = 0 then
    eqToHom (congrArg (ringedKoszulFactor O s m).X h) ≫
      (HomologicalComplex.doubleXIso₀ _ _).hom ≫
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 _).inv ≫
      eqToHom (congrArg (ringedSiteRingComplex O).X h.symm)
  else 0

/-- The degree-zero projection commutes with the differential.
Proof: the target differential is zero and the source differential lands in degree one,
where the projection vanishes. All other squares have a zero component.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulFactorProjectionF_comm
    (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulFactorProjectionF O s m n ≫ (ringedSiteRingComplex O).d n k =
      (ringedKoszulFactor O s m).d n k ≫ ringedKoszulFactorProjectionF O s m k := by
  rw [HomologicalComplex.single_obj_d, comp_zero]
  by_cases hn : n = 0
  · subst n
    have hk : k = 1 := by simpa using h.symm
    subst k
    simp [ringedKoszulFactorProjectionF]
  · rw [show (ringedKoszulFactor O s m).d n k = 0 from
      HomologicalComplex.double_d_eq_zero₀ _ _ _ _ hn, zero_comp]

/-- The augmented positive Koszul factor.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulFactorProjection (s : (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedKoszulFactor O s m ⟶ ringedSiteRingComplex O where
  f := ringedKoszulFactorProjectionF O s m
  comm' := ringedKoszulFactorProjectionF_comm O s m

/-- The ordinary unit identification O[0] tensor O[0] = O[0].
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulUnitTensorIso :
    ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).obj (ringedSiteRingComplex O) ≅
      ringedSiteRingComplex O :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.leftUnitor _

/-- Tensor the degree-zero projections, using the ordinary unit identification.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulProjection : (r : ℕ) →
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) →
      (m : ℕ) → (ringedKoszulDiagram O r b).obj m ⟶ ringedSiteRingComplex O :=
  fun r ↦ Nat.rec
    (fun _ _ ↦ 𝟙 _)
    (fun _ ih b m ↦
      ((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) m)).app _ ≫
        ((ringedKoszulTensor O).obj _).map (ih (fun i ↦ b i.succ) m) ≫
        (ringedKoszulUnitTensorIso O).hom) r

/-- The Koszul projections are compatible with the forward transitions.
Proof: in one factor, the forward map is identity in degree zero. Tensor this identity
and induct on the number of factors; composition gives the identity for every transition.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulProjection_naturality (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (m n : ℕ) (f : m ⟶ n) :
    (ringedKoszulDiagram O r b).map f ≫ ringedKoszulProjection O r b n =
      ringedKoszulProjection O r b m := by
  have hf (s : (O.obj ⋙ forget CommRingCat).sections) :
      (ringedKoszulFactors O s).map f ≫ ringedKoszulFactorProjection O s n =
        ringedKoszulFactorProjection O s m := by
    let e : ringedKoszulFactors O s ⟶ (Functor.const ℕ).obj (ringedSiteRingComplex O) :=
      NatTrans.ofSequence (fun j ↦ ringedKoszulFactorProjection O s j) (fun j ↦ by
        change (ringedKoszulFactors O s).map _ ≫ _ = _ ≫ 𝟙 _
        rw [show (ringedKoszulFactors O s).map (homOfLE (Nat.le_add_right j 1)) =
          ringedKoszulFactorStep O s j from Functor.ofSequence_map_homOfLE_succ _ j,
          Category.comp_id]
        apply HomologicalComplex.from_double_hom_ext
        · simp [ringedKoszulFactorStep, ringedKoszulFactorProjection,
            ringedKoszulFactorStepF, ringedKoszulFactorProjectionF, Category.assoc]
        · simp [ringedKoszulFactorStep, ringedKoszulFactorProjection,
            ringedKoszulFactorStepF, ringedKoszulFactorProjectionF])
    have he := e.naturality f
    change (ringedKoszulFactors O s).map f ≫ ringedKoszulFactorProjection O s n =
      ringedKoszulFactorProjection O s m ≫ 𝟙 _ at he
    simpa only [Category.comp_id] using he
  induction r with
  | zero => simp [ringedKoszulDiagram, ringedKoszulProjection]
  | succ r ih =>
    change
      (((ringedKoszulTensor O).map ((ringedKoszulFactors O (b 0)).map f)).app
          ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).obj m) ≫
        ((ringedKoszulTensor O).obj (ringedKoszulFactor O (b 0) n)).map
          ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).map f)) ≫
      (((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) n)).app
          ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).obj n) ≫
        ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).map
          (ringedKoszulProjection O r (fun i ↦ b i.succ) n) ≫
        (ringedKoszulUnitTensorIso O).hom) =
      ((ringedKoszulTensor O).map (ringedKoszulFactorProjection O (b 0) m)).app
          ((ringedKoszulDiagram O r (fun i ↦ b i.succ)).obj m) ≫
        ((ringedKoszulTensor O).obj (ringedSiteRingComplex O)).map
          (ringedKoszulProjection O r (fun i ↦ b i.succ) m) ≫
        (ringedKoszulUnitTensorIso O).hom
    simp only [Category.assoc]
    rw [NatTrans.naturality_assoc, ← NatTrans.comp_app_assoc,
      ← Functor.map_comp, hf, ← Functor.map_comp_assoc, ih]

/-- The compatible Koszul projections as an actual cocone.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulAugmentationCocone (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    Cocone (ringedKoszulDiagram O r b) where
  pt := ringedSiteRingComplex O
  ι :=
    { app := ringedKoszulProjection O r b
      naturality := ringedKoszulProjection_naturality O r b }

/-- The strict tensor tower N tensor Hom(P_m,O), functorial in N.
Its morphisms are total tensors with the dual transitions.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorTower (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O ⥤ (ℕᵒᵖ ⥤ ringedSiteComplex O) :=
  ringedKoszulTensor O ⋙
    (Functor.whiskeringLeft ℕᵒᵖ (ringedSiteComplex O) (ringedSiteComplex O)).obj
      (ringedKoszulDualTower O r b)

/-- The strict-tower differentials square to zero.
Proof: evaluate at every tower index and use the square-zero identity of its complex.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulTensorTower_d_comp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (n : ℤ) :
    Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
        (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) n (n + 1)) ≫
      Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
        (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) (n + 1) (n + 1 + 1)) = 0 := by
  apply NatTrans.ext
  funext m
  exact (((ringedKoszulTensorTower O r b).obj N).obj m).d_comp_d _ _ _

/-- The strict tensor tower, transposed into a complex in the abelian category of towers.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorTowerComplex (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ :=
  CochainComplex.of
    (fun n ↦ (ringedKoszulTensorTower O r b).obj N ⋙
      HomologicalComplex.eval _ (ComplexShape.up ℤ) n)
    (fun n ↦ Functor.whiskerLeft ((ringedKoszulTensorTower O r b).obj N)
      (HomologicalComplex.dNatTrans _ (ComplexShape.up ℤ) n (n + 1)))
    (ringedKoszulTensorTower_d_comp O r b N)

/-- Degreewise components of the strict tensor-tower map induced by a chain map.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorTowerComplexMapF (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (n : ℤ) :
    (ringedKoszulTensorTowerComplex O r b N).X n ⟶
      (ringedKoszulTensorTowerComplex O r b M).X n :=
  Functor.whiskerRight ((ringedKoszulTensorTower O r b).map f)
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)

/-- Tensor-tower maps commute with the differentials.
Proof: evaluate at each tower index and use the chain-map identity of the tensor map.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulTensorTowerComplexMapF_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) (n k : ℤ)
    (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulTensorTowerComplexMapF O r b f n ≫
        (ringedKoszulTensorTowerComplex O r b M).d n k =
      (ringedKoszulTensorTowerComplex O r b N).d n k ≫
        ringedKoszulTensorTowerComplexMapF O r b f k := by
  apply NatTrans.ext
  funext m
  have hk : n + 1 = k := h
  subst k
  simp [ringedKoszulTensorTowerComplexMapF, ringedKoszulTensorTowerComplex,
    CochainComplex.of_d]

/-- The actual strict map of tower complexes induced by a chain map.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorTowerComplexMap (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M : ringedSiteComplex O} (f : N ⟶ M) :
    ringedKoszulTensorTowerComplex O r b N ⟶ ringedKoszulTensorTowerComplex O r b M where
  f := ringedKoszulTensorTowerComplexMapF O r b f
  comm' := ringedKoszulTensorTowerComplexMapF_comm O r b f

/-- The strict tensor-tower construction preserves identity maps.
Proof: evaluate in each tower index and degree and use the identity law of the tensor functor.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulTensorTowerComplexMap_id (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    ringedKoszulTensorTowerComplexMap O r b (𝟙 N) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply NatTrans.ext
  funext m
  change (((ringedKoszulTensorTower O r b).map (𝟙 N)).app m).f n = 𝟙 _
  rw [Functor.map_id]
  rfl

/-- The strict tensor-tower construction preserves composition.
Proof: evaluate in each tower index and degree and use functoriality of total tensor.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulTensorTowerComplexMap_comp (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    {N M L : ringedSiteComplex O} (f : N ⟶ M) (g : M ⟶ L) :
    ringedKoszulTensorTowerComplexMap O r b (f ≫ g) =
      ringedKoszulTensorTowerComplexMap O r b f ≫
        ringedKoszulTensorTowerComplexMap O r b g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply NatTrans.ext
  funext m
  change (((ringedKoszulTensorTower O r b).map (f ≫ g)).app m).f n = _
  rw [Functor.map_comp]
  rfl

/-- The functor from module complexes to strict tensor-tower complexes.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorTowerFunctor (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) :
    ringedSiteComplex O ⥤ CochainComplex (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ℤ where
  obj := ringedKoszulTensorTowerComplex O r b
  map := ringedKoszulTensorTowerComplexMap O r b
  map_id := ringedKoszulTensorTowerComplexMap_id O r b
  map_comp := ringedKoszulTensorTowerComplexMap_comp O r b

/-- The degree-zero unit O[0] to the dual Koszul complex,
obtained by dualizing the projection P_m to O[0] and evaluation at one.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulDualUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (m : ℕ) :
    ringedSiteRingComplex O ⟶ (ringedKoszulDualTower O r b).obj (op m) :=
  (ringedHomUnitEvaluationIso O (ringedSiteRingComplex O)).inv ≫
    ((homComplexFunctor (R := O)).map (ringedKoszulProjection O r b m).op).app _

/-- The canonical total-tensor right unit isomorphism.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulRightUnitIso (N : ringedSiteComplex O) :
    ((ringedKoszulTensor O).obj N).obj (ringedSiteRingComplex O) ≅ N :=
  letI : IsGrothendieckAbelian.{u} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) :=
    SheafOfModules.isGrothendieckAbelian _
  letI := SheafOfModules.monoidalCategory O
  letI := SheafOfModules.symmetricCategory O
  letI := Classical.choice (SheafOfModules.tensorClosed O).1
  letI := Classical.choice (SheafOfModules.tensorClosed O).2.1
  HomologicalComplex.rightUnitor _

/-- The actual map N to N tensor Q_m induced by its degree-zero unit.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorUnitComponent (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (m : ℕᵒᵖ) :
    N ⟶ ((ringedKoszulTensorTower O r b).obj N).obj m :=
  (ringedKoszulRightUnitIso O N).inv ≫
    ((ringedKoszulTensor O).obj N).map (ringedKoszulDualUnit O r b m.unop)

/-- The degree-zero units form a cone over the strict tensor tower.
Proof: dualize compatibility of the Koszul projections with transitions, then tensor by N.
Taking the component in degree n gives the asserted equality.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulTensorUnitComponent_naturality (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) {m k : ℕᵒᵖ} (f : m ⟶ k) :
    ((Functor.const ℕᵒᵖ).obj (N.X n)).map f ≫
        (ringedKoszulTensorUnitComponent O r b N k).f n =
      (ringedKoszulTensorUnitComponent O r b N m).f n ≫
        ((ringedKoszulTensorTowerComplex O r b N).X n).map f := by
  have hd : ringedKoszulDualUnit O r b k.unop =
      ringedKoszulDualUnit O r b m.unop ≫ (ringedKoszulDualTower O r b).map f := by
    dsimp [ringedKoszulDualUnit, ringedKoszulDualTower]
    rw [Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, ← op_comp,
      ringedKoszulProjection_naturality]
  have hu : ringedKoszulTensorUnitComponent O r b N k =
      ringedKoszulTensorUnitComponent O r b N m ≫
        ((ringedKoszulTensorTower O r b).obj N).map f := by
    dsimp [ringedKoszulTensorUnitComponent, ringedKoszulTensorTower]
    rw [Category.assoc, ← Functor.map_comp, ← hd]
  simpa [ringedKoszulTensorTowerComplex] using congrArg (fun g ↦ g.f n) hu

/-- The compatible degree-zero maps as a degreewise cone over the strict tensor tower.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulTensorUnitCone (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) :
    Cone ((ringedKoszulTensorTowerComplex O r b N).X n) where
  pt := N.X n
  π :=
    { app := fun m ↦ (ringedKoszulTensorUnitComponent O r b N m).f n
      naturality := fun {_m _k} f ↦
        ringedKoszulTensorUnitComponent_naturality O r b N n f }

/-- The canonical degreewise map to the ordinary strict inverse limit.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulLimitUnitF (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n : ℤ) :
    N.X n ⟶ ((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N) |>.X n :=
  @id (N.X n ⟶ limit ((ringedKoszulTensorTowerComplex O r b N).X n))
    (limit.lift _ (ringedKoszulTensorUnitCone O r b N n))

/-- The map to the ordinary inverse limit is a chain map.
Proof: compose with each limit projection and use the chain-map identity of the degree-zero
unit into each tensor complex. Joint monicity of limit projections gives the equality.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
theorem ringedKoszulLimitUnitF_comm (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    (N : ringedSiteComplex O) (n k : ℤ) (h : (ComplexShape.up ℤ).Rel n k) :
    ringedKoszulLimitUnitF O r b N n ≫
        (((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N)).d n k =
      N.d n k ≫ ringedKoszulLimitUnitF O r b N k := by
  have hk : n + 1 = k := h
  subst k
  change limit.lift ((ringedKoszulTensorTowerComplex O r b N).X n)
      (ringedKoszulTensorUnitCone O r b N n) ≫
        limMap ((ringedKoszulTensorTowerComplex O r b N).d n (n + 1)) =
    N.d n (n + 1) ≫
      limit.lift ((ringedKoszulTensorTowerComplex O r b N).X (n + 1))
        (ringedKoszulTensorUnitCone O r b N (n + 1))
  apply limit.hom_ext
  intro m
  rw [Category.assoc, limMap_π, ← Category.assoc, limit.lift_π,
    Category.assoc, limit.lift_π]
  simp [ringedKoszulTensorUnitCone, ringedKoszulTensorTowerComplex,
    CochainComplex.of_d]

/-- The canonical ordinary strict-limit unit, before deriving inverse limit.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulLimitUnit (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O) :
    N ⟶ ((lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (ringedKoszulTensorTowerComplex O r b N) where
  f := ringedKoszulLimitUnitF O r b N
  comm' := ringedKoszulLimitUnitF_comm O r b N

/-- Restrict a global section to the slice site by its underlying compatible sections.
Source: Stacks Project, Tags 0913 and 0A0A
(auxiliary; not a blueprint node). -/
def ringedKoszulSliceSection (s : (O.obj ⋙ forget CommRingCat).sections) (U : C) :
    ((O.over U).obj ⋙ forget CommRingCat).sections :=
  ⟨fun V ↦ s.val (op V.unop.left), fun f ↦ s.property f.unop.left.op⟩

/-- Derived restriction between the two slice sites, along the actual overMap functor.
Source: Stacks Project, Tag 08JB
(auxiliary; not a blueprint node). -/
def ringedKoszulDerivedOverMap {U V : C} (f : V ⟶ U)
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    [hV : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] :
    ringedSiteDerived (O.over U) ⥤ ringedSiteDerived (O.over V) :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) := hV
  (SheafOfModules.overMap.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f).mapDerivedCategory

/-- The canonical composition isomorphism between successive and direct slice restrictions.
Source: Stacks Project, Tag 08JB
(auxiliary; not a blueprint node). -/
def ringedKoszulDerivedOverComparison {U V : C} (f : V ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [hU : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    [hV : HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over V) (forget₂ CommRingCat RingCat)).obj (O.over V)))] :
    ringedDerivedRestriction O U ⋙ ringedKoszulDerivedOverMap O f ≅
      ringedDerivedRestriction O V :=
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) := hU
  letI : HasDerivedCategory.{w} (SheafOfModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over V)) := hV
  (Functor.mapDerivedCategoryCompIso
    (SheafOfModules.overFunctor.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) U)
    (SheafOfModules.overMap.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f)) ≪≫
    Functor.mapDerivedCategoryNatIso
      (SheafOfModules.overFunctorMap
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O) f)

/-- A presentation of derived Koszul completion by a strict tensor tower and total right
derived inverse limit. The factorization fixes the strict tower including its transitions.
The right-derived universal property and computation on K-injective towers fix inverse
limit up to its unique normalized comparison isomorphism.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(auxiliary; not a blueprint node). -/
structure RingedKoszulLimitPresentation (r : ℕ)
    (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] where
  tensorTower : ringedSiteDerived O ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
  tensorFactors : DerivedCategory.Q ⋙ tensorTower ≅
    ringedKoszulTensorTowerFunctor O r b ⋙ DerivedCategory.Q
  inverseLimit : DerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ ringedSiteDerived O
  comparison :
    (lim : (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) ⥤ _).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ inverseLimit
  isRightDerived : inverseLimit.IsRightDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)) (ComplexShape.up ℤ))
  comparison_isIso : ∀ I, CochainComplex.IsKInjective I → IsIso (comparison.app I)

variable {O}

namespace RingedKoszulLimitPresentation

variable {r : ℕ} {b : Fin r → (O.obj ⋙ forget CommRingCat).sections}
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable (D : RingedKoszulLimitPresentation O r b)

/-- Compose the descended strict tensor-tower functor with total derived inverse limit.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(auxiliary; not a blueprint node). -/
def completion : ringedSiteDerived O ⥤ ringedSiteDerived O :=
  D.tensorTower ⋙ D.inverseLimit

/-- The canonical strict derived-limit unit on a representative complex.
Apply the derived-functor comparison to the actual map into the ordinary inverse limit,
then use the specified localization factorization of the strict tensor tower.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(auxiliary; not a blueprint node). -/
def unitOnComplex (N : ringedSiteComplex O) :
    DerivedCategory.Q.obj N ⟶ D.completion.obj (DerivedCategory.Q.obj N) :=
  DerivedCategory.Q.map (ringedKoszulLimitUnit O r b N) ≫
    D.comparison.app (ringedKoszulTensorTowerComplex O r b N) ≫
    D.inverseLimit.map (D.tensorFactors.app N).inv

/-- The canonical strict derived-limit unit on a derived object, using its localization
representative and transporting back along its specified representative isomorphism.
Source: Stacks Project, Tags 0913, 0A0A and 0941
(auxiliary; not a blueprint node). -/
def unit (E : ringedSiteDerived O) : E ⟶ D.completion.obj E :=
  (DerivedCategory.Q.objObjPreimageIso E).inv ≫
    D.unitOnComplex (DerivedCategory.Q.objPreimage E) ≫
    D.completion.map (DerivedCategory.Q.objObjPreimageIso E).hom

end RingedKoszulLimitPresentation

end CategoryTheory
