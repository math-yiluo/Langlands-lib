import Langlands.Geometry.FormalGroup.DrinfeldActionChartFormula

/-! # Preservation of the original framed comparisons by Drinfeld's formula -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s w

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

open CategoryTheory

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {D : Type w} [Ring D] [Algebra O D]
variable {σ τ : Type} [Finite σ] [Finite τ] {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction D X} {E' : OrderAction D Y}

attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem basicComparison_eq {a b : BasicAtlas.Comparison X Y}
    (hl : a.left = b.left) (hr : a.right = b.right)
    (hf : HEq a.coordinateIso.hom b.coordinateIso.hom)
    (hi : HEq a.coordinateIso.inv b.coordinateIso.inv) : a = b := by
  rcases a with ⟨l, r, _, ⟨f, f', _, _⟩⟩
  rcases b with ⟨l', r', _, ⟨g, g', _, _⟩⟩
  dsimp only at hl hr hf hi
  subst l'
  subst r'
  cases eq_of_heq hf
  cases eq_of_heq hi
  rfl

/-- Simultaneous conjugation retains the same refinements and whole underlying formal isomorphism. -/
theorem toBasicComparison_twist (c : Comparison E E') (α : D ≃ₐ[O] D) :
    (c.twist α).toBasicComparison = c.toBasicComparison := by
  refine basicComparison_eq (a := (c.twist α).toBasicComparison) (b := c.toBasicComparison) ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · apply heq_of_eq
    apply BasicAtlas.Hom.ext
    intro C b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    rfl
  · apply heq_of_eq
    apply BasicAtlas.Hom.ext
    intro C b hb
    apply ModuleLaw.Hom.ext
    apply CommLaw.Hom.ext
    rfl

private theorem toBasicComparison_baseChange_twist
    (c : Comparison E E') (V : CommAlgCat.{v} R) (α : D ≃ₐ[O] D) :
    ((c.twist α).baseChange V).toBasicComparison = (c.baseChange V).toBasicComparison :=
  ((c.twist α).toBasicComparison_baseChange V).trans
    ((congrArg (fun f : BasicAtlas.Comparison X Y => f.baseChange V) (c.toBasicComparison_twist α)).trans
      (c.toBasicComparison_baseChange V).symm)

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction.Comparison

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open CategoryTheory ValuativeRel ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R S : Type v} [CommRing R] [CommRing S]

private theorem reAlgebraComparison_toBasic_congr
    {α β : Algebra 𝒪[K] R} (e : α = β)
    {T U T' U' : (letI := α; SpecialAtlas K D ι R)}
    (c : (letI := α; Comparison T U)) (d : (letI := α; Comparison T' U'))
    (h : HEq (letI := α; c.toBasicComparison) (letI := α; d.toBasicComparison)) :
    HEq (letI := β; (reAlgebraComparison c β e).toBasicComparison)
      (letI := β; (reAlgebraComparison d β e).toBasicComparison) := by
  cases e
  exact h

variable [Algebra 𝒪[K] R]
variable {T U : SpecialAtlas K D ι R}

private theorem baseChangeComparison_twist_toBasic
    (c : Comparison T U) (V : CommAlgCat.{v} R) (d : Dˣ) :
    HEq (baseChangeComparison (c.twistDivisionUnit d) V).toBasicComparison
      (baseChangeComparison c V).toBasicComparison :=
  heq_of_eq (BasicAtlas.OrderAction.Comparison.toBasicComparison_baseChange_twist c V (conjugation K D d))

variable [Algebra 𝒪[K] S]

set_option maxHeartbeats 400000 in
/-- Changing the order by the same division-unit conjugation at both targets retains
both refinements and the actual underlying coefficient-extended formal comparison. -/
theorem Comparison.twistDivisionUnit_baseChangeAlong_toBasic
    (c : Comparison T U) (f : R →ₐ[𝒪[K]] S) (d : Dˣ) :
    HEq (baseChangeAlongComparison (c.twistDivisionUnit d) f).toBasicComparison
      (baseChangeAlongComparison c f).toBasicComparison := by
  let V := BasicAtlas.coefficientTest f
  exact reAlgebraComparison_toBasic_congr (BasicAtlas.coefficientAlgebraAlong_eq f)
    (baseChangeComparison (c.twistDivisionUnit d) V) (baseChangeComparison c V)
    (baseChangeComparison_twist_toBasic c V d)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas

namespace Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas

open CategoryTheory ValuativeRel CentralSimple ModuleLaw

attribute [local instance] coefficientAlgebra coefficientScalarTower

section ChartSquare

variable {O : Type u} [CommRing O] {S : Type v} [CommRing S] [Algebra O S]
variable {F : Type w} [Field F] [Algebra O F]
variable {σ τ ν : Type} [Finite σ] [Finite τ] [Finite ν]
variable {C : CommAlgCat.{v} S} {M M' N N' : ModuleLaw O C ν}
variable {T T' : BasicAtlas O S σ} {U U' : BasicAtlas O S τ}

private abbrev ChartFramings (M : ModuleLaw O C ν) (T : BasicAtlas O S σ) :=
  ∀ (a : T.opens) (ha : IsUnit (algebraMap S C a.val)),
    ModuleLaw.RationalHom F M ((T.chart a).map (BasicAtlas.coefficientLift (O := O) a.val C ha))

private def refinedTensor (q : BasicAtlas.CoverRefinement T)
    (f : ChartFramings (F := F) M T) (a : q.opens) (ha : IsUnit (algebraMap S C a.val)) :=
  ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (q.chartIso C a ha).inv)
    (f (q.source a) (q.source_unit C a ha))

private def forwardSquareOnChart (d : BasicAtlas.Comparison T U)
    (f : ChartFramings (F := F) M T) (g : ChartFramings (F := F) N U)
    (s : ModuleLaw.RationalHom F M N)
    (b : d.right.opens) (hb : IsUnit (algebraMap S C b.val)) : Prop :=
  let a := BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b
  ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (d.coordinateIso.hom.hom C b hb))
    (refinedTensor d.left f a hb) = ModuleLaw.RationalHom.comp (refinedTensor d.right g b hb) s

private theorem refinedTensor_precomp (q : BasicAtlas.CoverRefinement T)
    (f : ChartFramings (F := F) M T) (f' : ChartFramings (F := F) M' T)
    (m : ModuleLaw.RationalHom F M' M)
    (h : ∀ a ha, f' a ha = ModuleLaw.RationalHom.comp (f a ha) m)
    (a : q.opens) (ha : IsUnit (algebraMap S C a.val)) :
    refinedTensor q f' a ha = ModuleLaw.RationalHom.comp (refinedTensor q f a ha) m := by
  unfold refinedTensor
  rw [h]
  exact (ModuleLaw.RationalHom.comp_assoc _ _ _).symm

/-- A square of whole coordinate tensors survives common precomposition and transport
of the very same comparison to equal underlying atlases. -/
private theorem forwardSquareOnChart_precomp (d : BasicAtlas.Comparison T U)
    (d' : BasicAtlas.Comparison T' U') (hT : T' = T) (hU : U' = U) (hd : HEq d' d)
    (f : ChartFramings (F := F) M T) (g : ChartFramings (F := F) N U)
    (f' : ChartFramings (F := F) M' T') (g' : ChartFramings (F := F) N' U')
    (s : ModuleLaw.RationalHom F M N) (s' : ModuleLaw.RationalHom F M' N')
    (m : ModuleLaw.RationalHom F M' M) (n : ModuleLaw.RationalHom F N' N)
    (hn : ModuleLaw.RationalHom.comp s m = ModuleLaw.RationalHom.comp n s')
    (hf : ∀ (a : T.opens) (a' : T'.opens), a'.val = a.val → ∀ ha ha',
      HEq (f' a' ha') (ModuleLaw.RationalHom.comp (f a ha) m))
    (hg : ∀ (b : U.opens) (b' : U'.opens), b'.val = b.val → ∀ hb hb',
      HEq (g' b' hb') (ModuleLaw.RationalHom.comp (g b hb) n))
    (hc : ∀ b hb, forwardSquareOnChart d f g s b hb)
    (b' : d'.right.opens) (hb' : IsUnit (algebraMap S C b'.val)) :
    forwardSquareOnChart d' f' g' s' b' hb' := by
  subst T'
  subst U'
  cases eq_of_heq hd
  let a := BasicAtlas.sourceChart (X := d.left.atlas) (Y := d.right.atlas) d.sameCover b'
  have hleft := refinedTensor_precomp d.left f f' m (fun x hx => eq_of_heq (hf x x rfl hx hx)) a hb'
  have hright := refinedTensor_precomp d.right g g' n (fun y hy => eq_of_heq (hg y y rfl hy hy)) b' hb'
  have hs := hc b' hb'
  change ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (d.coordinateIso.hom.hom C b' hb'))
    (refinedTensor d.left f a hb') = ModuleLaw.RationalHom.comp (refinedTensor d.right g b' hb') s at hs
  change ModuleLaw.RationalHom.comp (ModuleLaw.RationalHom.ofHom (d.coordinateIso.hom.hom C b' hb'))
    (refinedTensor d.left f' a hb') = ModuleLaw.RationalHom.comp (refinedTensor d.right g' b' hb') s'
  rw [hleft, hright, ← ModuleLaw.RationalHom.comp_assoc, hs]
  simp only [ModuleLaw.RationalHom.comp_assoc, hn]

end ChartSquare

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] {π : 𝒪[K]}
variable {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}
variable {X Y : DrinfeldFramedAtlas Φ A}

set_option quotPrecheck false in
local notation "R₀" => ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj

private def chartFramings (X : DrinfeldFramedAtlas Φ A) (C : CommAlgCat.{u} R₀) :
    ChartFramings (F := K) (X.globalFrame.formalModule.map (IsScalarTower.toAlgHom 𝒪[K] R₀ C))
      X.target.val.reduction.atlas :=
  fun b hb => (X.chartFraming C b hb).hom.val

private def testFrameForward {a b : κ →ₐ[𝒪[K]] R₀} (e : a = b) (C : CommAlgCat.{u} R₀) :
    ModuleLaw.RationalHom K ((Φ.val.formalModule.map a).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C))
      ((Φ.val.formalModule.map b).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C)) := by
  subst b
  exact ModuleLaw.RationalHom.id _

private theorem globalFrameIso_forward (e : X.residueMap = Y.residueMap) (C : CommAlgCat.{u} R₀) :
    ModuleLaw.RationalHom.ofHom (F := K)
      ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C)).hom.val =
        testFrameForward (Φ := Φ) e C := by
  cases X
  cases Y
  cases e
  change ModuleLaw.RationalHom.ofHom
    (((ModuleLaw.OrderAction.Hom.id _).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C)).val) = _
  rw [ModuleLaw.OrderAction.Hom.map_id]
  rfl

private theorem refinedChartFraming_forward (X : DrinfeldFramedAtlas Φ A)
    (q : BasicAtlas.CoverRefinement X.target.val.reduction.atlas)
    (C : CommAlgCat.{u} R₀) (b : q.opens) (hb : IsUnit (algebraMap R₀ C b.val)) :
    (X.refinedChartFraming q C b hb).hom.val = refinedTensor q (chartFramings X C) b hb := rfl

private theorem reducedComparisonOnChart_forward
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (C : CommAlgCat.{u} R₀) (b : c.right.opens) (hb : IsUnit (algebraMap R₀ C b.val)) :
    (reducedComparisonOnChart (X := X) (Y := Y) c C b hb).hom.val =
      ModuleLaw.RationalHom.ofHom (F := K) (c.toBasicComparison.coordinateIso.hom.hom C b hb) := by
  have h := BasicAtlas.RationalHom.onChart_ofHom (F := K) (X := c.left.atlas) (Y := c.right.atlas)
    (h := c.sameCover) C b hb c.coordinateIso.hom.val
  exact h

set_option maxHeartbeats 800000 in
private theorem reducedFramingSquare_onChart_iff (e : X.residueMap = Y.residueMap)
    (c : SpecialAtlas.Comparison X.target.val.reduction Y.target.val.reduction)
    (C : CommAlgCat.{u} R₀) (b : c.right.opens) (hb : IsUnit (algebraMap R₀ C b.val)) :
    let a := BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b
    (X.refinedChartFraming c.left C a hb).trans (reducedComparisonOnChart (X := X) (Y := Y) c C b hb) =
      (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
        ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C))).trans
          (Y.refinedChartFraming c.right C b hb) ↔
      forwardSquareOnChart c.toBasicComparison (chartFramings X C) (chartFramings Y C)
        (testFrameForward (Φ := Φ) e C) b hb := by
  let a := BasicAtlas.sourceChart (X := c.left.atlas) (Y := c.right.atlas) c.sameCover b
  let q := (X.refinedChartFraming c.left C a hb).trans
    (reducedComparisonOnChart (X := X) (Y := Y) c C b hb)
  let q' := (ModuleLaw.OrderAction.QuasiIsogeny.ofIso
    ((globalFrameIso e).map (IsScalarTower.toAlgHom 𝒪[K] R₀ C))).trans
      (Y.refinedChartFraming c.right C b hb)
  let l := refinedTensor c.left (chartFramings X C) a hb
  let t := ModuleLaw.RationalHom.ofHom (F := K) (c.toBasicComparison.coordinateIso.hom.hom C b hb)
  let r := refinedTensor c.right (chartFramings Y C) b hb
  have hl : q.hom.val = ModuleLaw.RationalHom.comp t l :=
    congrArg₂ ModuleLaw.RationalHom.comp (reducedComparisonOnChart_forward (X := X) (Y := Y) c C b hb)
      (refinedChartFraming_forward X c.left C a hb)
  have hr : q'.hom.val = ModuleLaw.RationalHom.comp r (testFrameForward (Φ := Φ) e C) :=
    congrArg₂ ModuleLaw.RationalHom.comp (refinedChartFraming_forward Y c.right C b hb)
      (globalFrameIso_forward e C)
  change (q = q') ↔
    (ModuleLaw.RationalHom.comp t l = ModuleLaw.RationalHom.comp r (testFrameForward (Φ := Φ) e C))
  constructor
  · intro h
    exact hl.symm.trans ((congrArg (fun z => z.hom.val) h).trans hr)
  · intro h
    exact ModuleLaw.OrderAction.QuasiIsogeny.ext
      (ModuleLaw.OrderAction.RationalHom.ext (hl.trans (h.trans hr.symm)))

variable [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))
variable (c : Φ.val.MatrixCoordinates)
variable (hRank : ∀ j : ℕ, RelativeFrobeniusIsogenyStatement Φ.val.formalModule p (f * j))

private def testActionSource (ψ : κ →ₐ[𝒪[K]] R₀) (C : CommAlgCat.{u} R₀) :=
  ModuleLaw.RationalHom.map (IsScalarTower.toAlgHom 𝒪[K] R₀ C)
    (DrinfeldResidue.actionSourceHom Φ g p hcard hFrob c (b := ψ) rfl)

/-- The same equality of residue homomorphisms induces equality after the shift. -/
theorem act_residue_eq (e : X.residueMap = Y.residueMap) :
    (X.act g p hcard hFrob hRank c).residueMap = (Y.act g p hcard hFrob hRank c).residueMap :=
  congrArg (DrinfeldResidue.shift (DrinfeldAction.exponent K D g)) e

private theorem testActionSource_residue {a b : κ →ₐ[𝒪[K]] R₀} (e : a = b) (C : CommAlgCat.{u} R₀) :
    ModuleLaw.RationalHom.comp (testFrameForward (Φ := Φ) e C)
      (testActionSource g p hcard hFrob c a C) =
      ModuleLaw.RationalHom.comp (testActionSource g p hcard hFrob c b C)
        (testFrameForward (Φ := Φ) (congrArg (DrinfeldResidue.shift (DrinfeldAction.exponent K D g)) e) C) := by
  subst b
  exact (ModuleLaw.RationalHom.id_comp _).trans (ModuleLaw.RationalHom.comp_id _).symm

set_option maxHeartbeats 800000 in
/-- The transformed framing square uses the original refinements and the twisted target comparison. -/
theorem FramingSquare.act {e : X.residueMap = Y.residueMap}
    {d : SpecialAtlas.Comparison X.target.val Y.target.val} (hd : FramingSquare e d) :
    FramingSquare (act_residue_eq g p hcard hFrob c hRank e) (d.twistDivisionUnit g.2) := by
  let X' := X.act g p hcard hFrob hRank c
  let Y' := Y.act g p hcard hFrob hRank c
  let e' := act_residue_eq g p hcard hFrob c hRank e
  let q := SpecialAtlas.reductionComparison d
  let q' := SpecialAtlas.reductionComparison (d.twistDivisionUnit g.2)
  have hq : HEq q'.toBasicComparison q.toBasicComparison :=
    d.twistDivisionUnit_baseChangeAlong_toBasic (Nilp.quotientO 𝒪[K] A) g.2
  intro C b hb
  apply (reducedFramingSquare_onChart_iff e' q' C b hb).2
  exact forwardSquareOnChart_precomp q.toBasicComparison q'.toBasicComparison
    (X.actionReduction_atlas g) (Y.actionReduction_atlas g) hq
    (chartFramings X C) (chartFramings Y C) (chartFramings X' C) (chartFramings Y' C)
    (testFrameForward (Φ := Φ) e C) (testFrameForward (Φ := Φ) e' C)
    (testActionSource g p hcard hFrob c X.residueMap C) (testActionSource g p hcard hFrob c Y.residueMap C)
    (testActionSource_residue g p hcard hFrob c e C)
    (fun a a' ea ha ha' => X.chartFraming_act_hom g p hcard hFrob c hRank C a a' ea ha ha')
    (fun a a' ea ha ha' => Y.chartFraming_act_hom g p hcard hFrob c hRank C a a' ea ha ha')
    (fun a ha => (reducedFramingSquare_onChart_iff e q C a ha).1 (hd C a ha)) b hb

/-- The specified comparison transforms with its actual target map and its framing square. -/
def Comparison.act (d : Comparison X Y) :
    Comparison (X.act g p hcard hFrob hRank c) (Y.act g p hcard hFrob hRank c) where
  targetComparison := d.targetComparison.twistDivisionUnit g.2
  residue_eq := act_residue_eq g p hcard hFrob c hRank d.residue_eq
  square := d.square.act g p hcard hFrob c hRank

end Langlands.FormalGroup.LocalDivision.DrinfeldFramedAtlas
