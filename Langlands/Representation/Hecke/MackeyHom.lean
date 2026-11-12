import Langlands.Representation.Hecke.MackeyCurrying
import Langlands.Representation.Hecke.HomomorphismProof

/-! # The Hom Mackey isomorphism, natural in both representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory MeasureTheory

namespace Langlands.Hecke.Homomorphism

universe uG uH v

section General

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {H : Type uH} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (φ : H →* G) (hφ : Continuous φ)
  {R : SmoothRep.{0, uH, v} ℂ H ⥤ SmoothRep.{0, uG, v} ℂ G}
  (adj : restriction φ hφ ⊣ R)

/-- The five Hom-set identifications of Renard (III.2.11.1)–(III.2.11.5). -/
def homMackeyEquiv (E V : SmoothRep.{0, uG, v} ℂ G)
    (W : SmoothRep.{0, uH, v} ℂ H) :
    (E ⟶ (smoothHomBifunctor G).obj (Opposite.op V, R.obj W)) ≃
      (E ⟶ R.obj ((smoothHomBifunctor H).obj
        (Opposite.op ((restriction φ hφ).obj V), W))) :=
  ((smoothCurry E V (R.obj W)).symm.trans (adj.homEquiv _ W).symm).trans
    ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V) W).trans
      (adj.homEquiv E _))

theorem homMackeyEquiv_left {E E' V : SmoothRep.{0, uG, v} ℂ G}
    (W : SmoothRep.{0, uH, v} ℂ H) (f : E' ⟶ E)
    (g : E ⟶ (smoothHomBifunctor G).obj (Opposite.op V, R.obj W)) :
    homMackeyEquiv φ hφ adj E' V W (f ≫ g) =
      f ≫ homMackeyEquiv φ hφ adj E V W g := by
  dsimp only [homMackeyEquiv, Equiv.trans_apply]
  rw [smoothUncurry_left f g, Adjunction.homEquiv_naturality_left_symm]
  let k : (smoothTensorBifunctor H).obj
      ((restriction φ hφ).obj E, (restriction φ hφ).obj V) ⟶ W :=
    (adj.homEquiv ((smoothTensorBifunctor G).obj (E, V)) W).symm
      ((smoothCurry E V (R.obj W)).symm g)
  change (adj.homEquiv E' _)
    ((smoothCurry ((restriction φ hφ).obj E') ((restriction φ hφ).obj V) W)
      ((smoothTensorBifunctor H).map
        (Prod.mkHom ((restriction φ hφ).map f) (𝟙 ((restriction φ hφ).obj V))) ≫ k)) =
    f ≫ (adj.homEquiv E _)
      ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V) W) k)
  rw [smoothCurry_left, Adjunction.homEquiv_naturality_left]

theorem homMackeyEquiv_first {E V V' : SmoothRep.{0, uG, v} ℂ G}
    (W : SmoothRep.{0, uH, v} ℂ H) (f : V' ⟶ V)
    (g : E ⟶ (smoothHomBifunctor G).obj (Opposite.op V, R.obj W)) :
    homMackeyEquiv φ hφ adj E V' W
        (g ≫ (smoothHomBifunctor G).map (Prod.mkHom f.op (𝟙 (R.obj W)))) =
      homMackeyEquiv φ hφ adj E V W g ≫ R.map
        ((smoothHomBifunctor H).map (Prod.mkHom ((restriction φ hφ).map f).op (𝟙 W))) := by
  dsimp only [homMackeyEquiv, Equiv.trans_apply]
  rw [smoothUncurry_middle f g, Adjunction.homEquiv_naturality_left_symm]
  let k : (smoothTensorBifunctor H).obj
      ((restriction φ hφ).obj E, (restriction φ hφ).obj V) ⟶ W :=
    (adj.homEquiv ((smoothTensorBifunctor G).obj (E, V)) W).symm
      ((smoothCurry E V (R.obj W)).symm g)
  change (adj.homEquiv E _)
    ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V') W)
      ((smoothTensorBifunctor H).map
        (Prod.mkHom (𝟙 ((restriction φ hφ).obj E)) ((restriction φ hφ).map f)) ≫ k)) =
    (adj.homEquiv E _)
      ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V) W) k) ≫
      R.map ((smoothHomBifunctor H).map
        (Prod.mkHom ((restriction φ hφ).map f).op (𝟙 W)))
  rw [smoothCurry_middle, Adjunction.homEquiv_naturality_right]

theorem homMackeyEquiv_second {E V : SmoothRep.{0, uG, v} ℂ G}
    {W W' : SmoothRep.{0, uH, v} ℂ H} (f : W ⟶ W')
    (g : E ⟶ (smoothHomBifunctor G).obj (Opposite.op V, R.obj W)) :
    homMackeyEquiv φ hφ adj E V W'
        (g ≫ (smoothHomBifunctor G).map (Prod.mkHom (𝟙 (Opposite.op V)) (R.map f))) =
      homMackeyEquiv φ hφ adj E V W g ≫ R.map
        ((smoothHomBifunctor H).map (Prod.mkHom (𝟙 (Opposite.op ((restriction φ hφ).obj V))) f)) := by
  dsimp only [homMackeyEquiv, Equiv.trans_apply]
  rw [smoothUncurry_right g (R.map f), Adjunction.homEquiv_naturality_right_symm]
  let k : (smoothTensorBifunctor H).obj
      ((restriction φ hφ).obj E, (restriction φ hφ).obj V) ⟶ W :=
    (adj.homEquiv ((smoothTensorBifunctor G).obj (E, V)) W).symm
      ((smoothCurry E V (R.obj W)).symm g)
  change (adj.homEquiv E _)
    ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V) W') (k ≫ f)) =
    (adj.homEquiv E _)
      ((smoothCurry ((restriction φ hφ).obj E) ((restriction φ hφ).obj V) W) k) ≫
      R.map ((smoothHomBifunctor H).map
        (Prod.mkHom (𝟙 (Opposite.op ((restriction φ hφ).obj V))) f))
  rw [smoothCurry_right, Adjunction.homEquiv_naturality_right]

/-- The Hom identity for the actual smooth bifunctor and any right adjoint of
continuous pullback, contravariantly natural in V and naturally in W. -/
def homMackeyIso :
    ((𝟭 (SmoothRep.{0, uG, v} ℂ G)ᵒᵖ).prod R) ⋙ smoothHomBifunctor G ≅
      ((restriction φ hφ).op.prod (𝟭 (SmoothRep.{0, uH, v} ℂ H))) ⋙
        smoothHomBifunctor H ⋙ R := by
  refine isoOfNaturalHomEquiv _ _
    (fun E X => homMackeyEquiv φ hφ adj E X.1.unop X.2)
    (fun _ f g => homMackeyEquiv_left φ hφ adj _ f g) ?_
  intro E X Y f g
  have hm : (smoothHomBifunctor G).map (Prod.mkHom f.1 (R.map f.2)) =
      (smoothHomBifunctor G).map (Prod.mkHom f.1 (𝟙 (R.obj X.2))) ≫
        (smoothHomBifunctor G).map (Prod.mkHom (𝟙 Y.1) (R.map f.2)) := by
    rw [← Functor.map_comp]
    congr 1
  change homMackeyEquiv φ hφ adj E Y.1.unop Y.2
    (g ≫ (smoothHomBifunctor G).map (Prod.mkHom f.1 (R.map f.2))) = _
  rw [hm, ← Category.assoc]
  change homMackeyEquiv φ hφ adj E Y.1.unop Y.2
    ((g ≫ (smoothHomBifunctor G).map (Prod.mkHom f.1.unop.op (𝟙 (R.obj X.2)))) ≫ _) = _
  rw [homMackeyEquiv_second, homMackeyEquiv_first, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp]
  congr 2

end General

section Hecke

variable {G : Type uG} [Group G] [TopologicalSpace G] [T2Space G]
  [NonarchimedeanGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {H : Type uH} [Group H] [TopologicalSpace H] [T2Space H]
  [NonarchimedeanGroup H] [LocallyCompactSpace H] [MeasurableSpace H] [BorelSpace H]
  (μG : Measure G) [μG.IsHaarMeasure] (μH : Measure H) [μH.IsHaarMeasure]
  (φ : H →* G) (hφ : Continuous φ)
  (eG : (heckeNondegenerateModuleFunctor.{uG, max uG v} μG).IsEquivalence)
  (eH : (heckeNondegenerateModuleFunctor.{uH, max uG v} μH).IsEquivalence)

/-- The unconditional Mackey Hom comparison for the published Hecke transport. -/
def heckeHomMackeyIso
    (adj : smoothF μG μH φ hφ eH ⊣ smoothI μG μH φ hφ eG) :
    mackeyHomLeft μG μH φ hφ eG ≅ mackeyHomRight μG μH φ hφ eG :=
  homMackeyIso φ hφ (adj.ofNatIsoLeft (smoothPullbackComparison μG μH φ hφ eH).symm)

end Hecke

end Langlands.Hecke.Homomorphism
