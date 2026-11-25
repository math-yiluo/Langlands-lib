import Langlands.GroupScheme.Cartier.FiniteDualPairingExt
import Langlands.GroupScheme.Cartier.FiniteSchemeDualBaseChange
import Langlands.AbelianScheme.Tate.BaseChangeCoherence

/-! # Coherence of the pullback comparison for finite Cartier duals -/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Cartier.FiniteDual

open GroupScheme.HomScheme

private def baseChangeCompAlong {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ X) (h : d = c ≫ b) :
    CommGroupScheme.baseChange d ≅ CommGroupScheme.baseChange b ⋙ CommGroupScheme.baseChange c :=
  eqToIso (congrArg CommGroupScheme.baseChange h) ≪≫
    NatIso.ofComponents (fun G => GroupScheme.CommGroupScheme.isoOfGroupIso
      (GroupScheme.baseChangeCompIso b c G.toGrp))
      (by
        intro G H f
        exact congrArg Additive.ofMul
          ((Functor.mapGrpNatIso (Over.pullbackComp c b) ≪≫
            Functor.mapGrpCompIso).hom.naturality f.toMul))

private def testCompositionAlong {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ X) (h : d = c ≫ b) (U : Over Z) :
    (Over.map b).obj ((Over.map c).obj U) ⟶ (Over.map d).obj U :=
  (Over.mapComp c b).inv.app U ≫ eqToHom (congrArg (fun a => (Over.map a).obj U) h.symm)

private theorem testCompositionAlong_left {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ X) (h : d = c ≫ b) (U : Over Z) :
    (testCompositionAlong b c d h U).left = 𝟙 U.left := by
  subst d
  simp [testCompositionAlong]

private theorem baseChangePointsEquiv_compAlong {X Y Z : Scheme.{u}}
    (b : Y ⟶ X) (c : Z ⟶ Y) (d : Z ⟶ X) (h : d = c ≫ b)
    (G : CommGroupScheme X) (U : Over Z)
    (x : U ⟶ ((CommGroupScheme.baseChange c).obj ((CommGroupScheme.baseChange b).obj G)).X) :
    baseChangePointsEquiv b G.toGrp ((Over.map c).obj U)
        (baseChangePointsEquiv c ((CommGroupScheme.baseChange b).obj G).toGrp U x) =
      testCompositionAlong b c d h U ≫
        baseChangePointsEquiv d G.toGrp U
          (x ≫ ((baseChangeCompAlong b c d h).app G).inv.toMul.hom.hom) := by
  subst d
  simp only [testCompositionAlong, eqToHom_refl, Category.comp_id, baseChangeCompAlong,
    eqToIso_refl, Iso.refl_trans, NatIso.ofComponents.app]
  exact GroupScheme.baseChangePointsEquiv_base_comp b c G.toGrp U x

private theorem baseChangePointsEquiv_compAlong_hom {X Y Z : Scheme.{u}}
    (f : Y ⟶ X) (g : Z ⟶ Y) (k : Z ⟶ X) (h : k = g ≫ f)
    (G : CommGroupScheme X) (U : Over Z)
    (z : U ⟶ ((CommGroupScheme.baseChange k).obj G).X) :
    let e := (baseChangeCompAlong f g k h).app G
    baseChangePointsEquiv f G.toGrp ((Over.map g).obj U)
        (baseChangePointsEquiv g ((CommGroupScheme.baseChange f).obj G).toGrp U
          (z ≫ e.hom.toMul.hom.hom)) =
      testCompositionAlong f g k h U ≫ baseChangePointsEquiv k G.toGrp U z := by
  let e := (baseChangeCompAlong f g k h).app G
  let a := testCompositionAlong f g k h U
  let m := e.hom.toMul.hom.hom
  let n := e.inv.toMul.hom.hom
  have he : m ≫ n = 𝟙 _ :=
    congrArg (fun f : (CommGroupScheme.baseChange k).obj G ⟶ (CommGroupScheme.baseChange k).obj G =>
      f.toMul.hom.hom) e.hom_inv_id
  have hz : (z ≫ m) ≫ n = z := by rw [Category.assoc, he, Category.comp_id]
  exact (baseChangePointsEquiv_compAlong f g k h G U (z ≫ m)).trans
    (congrArg (fun y => a ≫ baseChangePointsEquiv k G.toGrp U y) hz)

local instance compBaseChangeFinite {X Y : Scheme.{u}} (a : Y ⟶ X)
    (G : CommGroupScheme X) [IsFinite G.X.hom] : IsFinite ((CommGroupScheme.baseChange a).obj G).X.hom := by
  change IsFinite (pullback.snd G.X.hom a)
  infer_instance

local instance compBaseChangeFlat {X Y : Scheme.{u}} (a : Y ⟶ X)
    (G : CommGroupScheme X) [Flat G.X.hom] : Flat ((CommGroupScheme.baseChange a).obj G).X.hom := by
  change Flat (pullback.snd G.X.hom a)
  infer_instance

local instance compBaseChangeFP {X Y : Scheme.{u}} (a : Y ⟶ X)
    (G : CommGroupScheme X) [LocallyOfFinitePresentation G.X.hom] :
    LocallyOfFinitePresentation ((CommGroupScheme.baseChange a).obj G).X.hom := by
  change LocallyOfFinitePresentation (pullback.snd G.X.hom a)
  infer_instance

private def pairingUnit {A : CommRingCat.{u}} (H : CommGroupScheme (Spec A))
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (U : Over (Spec A)) (z : U ⟶ (schemeDual H).X) (x : U ⟶ H.X) : (Γ(U.left, ⊤))ˣ :=
  Gm.pointsEquiv _ U (finiteSchemePairing H U z x)

private theorem pairingUnit_dualMap {A : CommRingCat.{u}}
    {H L : CommGroupScheme (Spec A)} [IsFinite H.X.hom] [Flat H.X.hom]
    [LocallyOfFinitePresentation H.X.hom] [IsFinite L.X.hom] [Flat L.X.hom]
    [LocallyOfFinitePresentation L.X.hom]
    (f : H ⟶ L) (U : Over (Spec A)) (x : U ⟶ H.X) (z : U ⟶ (schemeDual L).X) :
    pairingUnit H U (z ≫ (schemeDualMap f).toMul.hom.hom) x =
      pairingUnit L U z (x ≫ f.toMul.hom.hom) :=
  congrArg (Gm.pointsEquiv _ U) (finiteSchemePairing_dualMap f U x z).symm

private theorem schemeDualHom_ext_of_pairing {A : CommRingCat.{u}} (H : CommGroupScheme (Spec A))
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    {L : CommGroupScheme (Spec A)} {f g : L ⟶ schemeDual H}
    (h : ∀ (U : Over (Spec A)) (z : U ⟶ L.X) (x : U ⟶ H.X),
      pairingUnit H U (z ≫ f.toMul.hom.hom) x = pairingUnit H U (z ≫ g.toMul.hom.hom) x) : f = g := by
  apply GroupScheme.CommGroupScheme.hom_ext_points
  intro U z
  apply schemeDualPoint_ext_of_pairing H
  intro V a x
  apply (Gm.pointsEquiv _ V).injective
  simpa only [pairingUnit, Category.assoc] using h V (a ≫ z) x

private theorem schemeDualHom_comp_eq_of_pairing {A : CommRingCat.{u}} (H : CommGroupScheme (Spec A))
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    {L M N P : CommGroupScheme (Spec A)} (i : L ⟶ M) (j : M ⟶ N) (k : N ⟶ schemeDual H)
    (l : L ⟶ P) (m : P ⟶ schemeDual H)
    (h : ∀ (U : Over (Spec A)) (z : U ⟶ L.X) (x : U ⟶ H.X),
      pairingUnit H U (((z ≫ i.toMul.hom.hom) ≫ j.toMul.hom.hom) ≫ k.toMul.hom.hom) x =
        pairingUnit H U ((z ≫ l.toMul.hom.hom) ≫ m.toMul.hom.hom) x) :
    i ≫ j ≫ k = l ≫ m := by
  apply schemeDualHom_ext_of_pairing H
  intro U z x
  change pairingUnit H U (z ≫ i.toMul.hom.hom ≫ j.toMul.hom.hom ≫ k.toMul.hom.hom) x =
    pairingUnit H U (z ≫ l.toMul.hom.hom ≫ m.toMul.hom.hom) x
  simpa only [Category.assoc] using h U z x

section Composition

variable {A B C : CommRingCat.{u}}
  (b : Spec B ⟶ Spec A) (c : Spec C ⟶ Spec B) (d : Spec C ⟶ Spec A) (h : d = c ≫ b)
  (G : CommGroupScheme (Spec A)) [IsFinite G.X.hom] [Flat G.X.hom]
  [LocallyOfFinitePresentation G.X.hom]

local notation "F" => CommGroupScheme.baseChange b
local notation "J" => CommGroupScheme.baseChange c
local notation "K" => CommGroupScheme.baseChange d

private theorem pairingUnit_compTest
    (U : Over (Spec C)) (z : (Over.map d).obj U ⟶ (schemeDual G).X)
    (x : (Over.map d).obj U ⟶ G.X) :
    let a := testCompositionAlong b c d h U
    pairingUnit G _ (a ≫ z) (a ≫ x) = pairingUnit G _ z x := by
  let a := testCompositionAlong b c d h U
  let U₂ := (Over.map b).obj ((Over.map c).obj U)
  let U₃ := (Over.map d).obj U
  have hn := finiteSchemePairing_naturality G a x z
  have hnUnits := Gm.pointsEquiv_naturality (Spec A) a (finiteSchemePairing G U₃ z x)
  have ha : a.left = 𝟙 U.left := testCompositionAlong_left b c d h U
  calc
    _ = Gm.pointsEquiv _ U₂ (a ≫ finiteSchemePairing G U₃ z x) :=
      congrArg (Gm.pointsEquiv _ U₂) hn
    _ = Units.map (Scheme.Hom.appTop a.left).hom.toMonoidHom
        (Gm.pointsEquiv _ U₃ (finiteSchemePairing G U₃ z x)) := hnUnits
    _ = _ := by
      have hid : Units.map (Scheme.Hom.appTop (𝟙 U.left)).hom.toMonoidHom =
          MonoidHom.id (Γ(U.left, ⊤))ˣ := by simp
      rw [ha, hid]
      rfl

/-- A morphism of a pulled-back dual preserves evaluation when it agrees with evaluation
on original points under the pullback adjunction. -/
private def PreservesEvaluation {A B : CommRingCat.{u}} (f : Spec B ⟶ Spec A)
    (L : CommGroupScheme (Spec A)) [IsFinite L.X.hom] [Flat L.X.hom]
    [LocallyOfFinitePresentation L.X.hom]
    (j : (CommGroupScheme.baseChange f).obj (schemeDual L) ⟶
      schemeDual ((CommGroupScheme.baseChange f).obj L)) : Prop :=
  ∀ (U : Over (Spec B)) (z : U ⟶ ((CommGroupScheme.baseChange f).obj (schemeDual L)).X)
    (x : U ⟶ ((CommGroupScheme.baseChange f).obj L).X),
    pairingUnit ((CommGroupScheme.baseChange f).obj L) U (z ≫ j.toMul.hom.hom) x =
      pairingUnit L ((Over.map f).obj U) (baseChangePointsEquiv f (schemeDual L).toGrp U z)
        (baseChangePointsEquiv f L.toGrp U x)

private theorem successivePairingUnit
    (j : (F).obj (schemeDual G) ⟶ schemeDual ((F).obj G)) (hj : PreservesEvaluation b G j)
    (k : (J).obj (schemeDual ((F).obj G)) ⟶ schemeDual ((J).obj ((F).obj G)))
    (hk : PreservesEvaluation c ((F).obj G) k)
    (U : Over (Spec C)) (z : U ⟶ ((J).obj ((F).obj (schemeDual G))).X)
    (x : U ⟶ ((J).obj ((F).obj G)).X) :
    let U₁ := (Over.map c).obj U
    let U₂ := (Over.map b).obj U₁
    pairingUnit ((J).obj ((F).obj G)) U ((z ≫ ((J).map j).toMul.hom.hom) ≫ k.toMul.hom.hom) x =
      pairingUnit G U₂
        (baseChangePointsEquiv b (schemeDual G).toGrp U₁
          (baseChangePointsEquiv c ((F).obj (schemeDual G)).toGrp U z))
        (baseChangePointsEquiv b G.toGrp U₁ (baseChangePointsEquiv c ((F).obj G).toGrp U x)) := by
  let G₁ := (F).obj G
  let G₂ := (J).obj G₁
  let U₁ := (Over.map c).obj U
  let U₂ := (Over.map b).obj U₁
  let z₁ := z ≫ ((J).map j).toMul.hom.hom
  let z₂ := baseChangePointsEquiv c ((F).obj (schemeDual G)).toGrp U z
  let x₁ := baseChangePointsEquiv c G₁.toGrp U x
  have hz : baseChangePointsEquiv c (schemeDual G₁).toGrp U z₁ = z₂ ≫ j.toMul.hom.hom :=
    baseChangePointsEquiv_comp c j.toMul U z
  calc
    pairingUnit G₂ U (z₁ ≫ k.toMul.hom.hom) x =
        pairingUnit G₁ U₁ (baseChangePointsEquiv c (schemeDual G₁).toGrp U z₁) x₁ := hk U z₁ x
    _ = pairingUnit G₁ U₁ (z₂ ≫ j.toMul.hom.hom) x₁ :=
      congrArg (fun y => pairingUnit G₁ U₁ y x₁) hz
    _ = pairingUnit G U₂ (baseChangePointsEquiv b (schemeDual G).toGrp U₁ z₂)
        (baseChangePointsEquiv b G.toGrp U₁ x₁) := hj U₁ z₂ x₁

private theorem directPairingUnit {H : CommGroupScheme (Spec C)}
    [IsFinite H.X.hom] [Flat H.X.hom] [LocallyOfFinitePresentation H.X.hom]
    (l : (K).obj (schemeDual G) ⟶ schemeDual ((K).obj G)) (hl : PreservesEvaluation d G l)
    (v : H ⟶ (K).obj G) (U : Over (Spec C))
    (z : U ⟶ ((K).obj (schemeDual G)).X) (x : U ⟶ H.X) :
    pairingUnit H U ((z ≫ l.toMul.hom.hom) ≫ (schemeDualMap v).toMul.hom.hom) x =
      pairingUnit G ((Over.map d).obj U) (baseChangePointsEquiv d (schemeDual G).toGrp U z)
        (baseChangePointsEquiv d G.toGrp U (x ≫ v.toMul.hom.hom)) :=
  (pairingUnit_dualMap v U x (z ≫ l.toMul.hom.hom)).trans (hl U z (x ≫ v.toMul.hom.hom))

set_option maxHeartbeats 1200000 in
private theorem pairingUnit_compareComposites
    (j : (F).obj (schemeDual G) ⟶ schemeDual ((F).obj G)) (hj : PreservesEvaluation b G j)
    (k : (J).obj (schemeDual ((F).obj G)) ⟶ schemeDual ((J).obj ((F).obj G)))
    (hk : PreservesEvaluation c ((F).obj G) k)
    (l : (K).obj (schemeDual G) ⟶ schemeDual ((K).obj G)) (hl : PreservesEvaluation d G l)
    (U : Over (Spec C)) (z : U ⟶ ((K).obj (schemeDual G)).X)
    (x : U ⟶ ((J).obj ((F).obj G)).X) :
    let i := ((baseChangeCompAlong b c d h).app (schemeDual G)).hom.toMul.hom.hom
    let v : (J).obj ((F).obj G) ⟶ (K).obj G := ((baseChangeCompAlong b c d h).app G).inv
    pairingUnit ((J).obj ((F).obj G)) U
        (((z ≫ i) ≫ ((J).map j).toMul.hom.hom) ≫ k.toMul.hom.hom) x =
      pairingUnit ((J).obj ((F).obj G)) U ((z ≫ l.toMul.hom.hom) ≫ (schemeDualMap v).toMul.hom.hom) x := by
  let U₁ := (Over.map c).obj U
  let U₂ := (Over.map b).obj U₁
  let U₃ := (Over.map d).obj U
  let v : (J).obj ((F).obj G) ⟶ (K).obj G := ((baseChangeCompAlong b c d h).app G).inv
  let i := ((baseChangeCompAlong b c d h).app (schemeDual G)).hom.toMul.hom.hom
  let z' := baseChangePointsEquiv d (schemeDual G).toGrp U z
  let x' := baseChangePointsEquiv d G.toGrp U (x ≫ v.toMul.hom.hom)
  let a := testCompositionAlong b c d h U
  have hz := baseChangePointsEquiv_compAlong_hom b c d h (schemeDual G) U z
  have hx := baseChangePointsEquiv_compAlong b c d h G U x
  calc
    _ = pairingUnit G U₂ (a ≫ z') (a ≫ x') :=
      (successivePairingUnit b c G j hj k hk U (z ≫ i) x).trans
        (congrArg₂ (pairingUnit G U₂) hz hx)
    _ = pairingUnit G U₃ z' x' := pairingUnit_compTest b c d h G U z' x'
    _ = _ := (directPairingUnit d G (H := (J).obj ((F).obj G)) l hl v U z x).symm

private theorem schemeDualBaseChangeComp_of_evaluation
    (j : (F).obj (schemeDual G) ⟶ schemeDual ((F).obj G)) (hj : PreservesEvaluation b G j)
    (k : (J).obj (schemeDual ((F).obj G)) ⟶ schemeDual ((J).obj ((F).obj G)))
    (hk : PreservesEvaluation c ((F).obj G) k)
    (l : (K).obj (schemeDual G) ⟶ schemeDual ((K).obj G)) (hl : PreservesEvaluation d G l) :
    ((baseChangeCompAlong b c d h).app (schemeDual G)).hom ≫ (J).map j ≫ k =
      l ≫ schemeDualMap (G := (J).obj ((F).obj G)) ((baseChangeCompAlong b c d h).app G).inv :=
  schemeDualHom_comp_eq_of_pairing ((J).obj ((F).obj G))
    ((baseChangeCompAlong b c d h).app (schemeDual G)).hom ((J).map j) k l
    (schemeDualMap (G := (J).obj ((F).obj G)) ((baseChangeCompAlong b c d h).app G).inv)
    (pairingUnit_compareComposites b c d h G j hj k hk l hl)

end Composition

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

local notation "b" => specBase R S
local notation "c" => specBase S T
local notation "d" => specBase R T
local notation "F" => CommGroupScheme.baseChange b
local notation "J" => CommGroupScheme.baseChange c
local notation "K" => CommGroupScheme.baseChange d

private theorem specBase_comp : d = c ≫ b := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- Direct and successive pullback of an affine-base commutative group scheme. -/
def affineBaseChangeCompIso (G : CommGroupScheme (Spec (CommRingCat.of R))) :
    (K).obj G ≅ (J).obj ((F).obj G) :=
  (baseChangeCompAlong b c d (specBase_comp (R := R) (S := S) (T := T))).app G

variable (G : CommGroupScheme (Spec (CommRingCat.of R)))
  [IsFinite G.X.hom] [Flat G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- The finite Cartier comparison is compatible with two successive affine pullbacks. -/
theorem schemeDualBaseChangeIso_comp :
    (affineBaseChangeCompIso (S := S) (T := T) (schemeDual G)).hom ≫
        (J).map (schemeDualBaseChangeIso (S := S) G).hom ≫
          (schemeDualBaseChangeIso (S := T) ((F).obj G)).hom =
      (schemeDualBaseChangeIso (S := T) G).hom ≫
        schemeDualMap (affineBaseChangeCompIso (S := S) (T := T) G).inv :=
  schemeDualBaseChangeComp_of_evaluation b c d (specBase_comp (R := R) (S := S) (T := T)) G
    (schemeDualBaseChangeIso (S := S) G).hom (schemeDualBaseChangeIso_evaluation (S := S) G)
    (schemeDualBaseChangeIso (S := T) ((F).obj G)).hom
    (schemeDualBaseChangeIso_evaluation (S := T) ((F).obj G))
    (schemeDualBaseChangeIso (S := T) G).hom (schemeDualBaseChangeIso_evaluation (S := T) G)

end Langlands.GroupScheme.Cartier.FiniteDual
