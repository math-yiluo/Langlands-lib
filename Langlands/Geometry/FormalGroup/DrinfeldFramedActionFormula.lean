import Langlands.Geometry.FormalGroup.AtlasRationalCoverDetection
import Langlands.Geometry.FormalGroup.DrinfeldActionExponent
import Langlands.Geometry.FormalGroup.DrinfeldMatrixFrame
import Langlands.Geometry.FormalGroup.DrinfeldSignedFrameFrobenius
import Langlands.Geometry.FormalGroup.SpecialAtlasDivisionAction

/-! # Whole quasi-isogenies in the Drinfeld framing formula -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v s

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel CentralDivision CentralSimple ModuleLaw
open scoped TensorProduct nonZeroDivisors

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]

attribute [local instance] coefficientAlgebra coefficientScalarTower

section Equivariance

variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas 𝒪[K] R σ} {Y : BasicAtlas 𝒪[K] R τ} {h : X.opens = Y.opens}
variable {E : BasicAtlas.OrderAction (IntegerRing K D) X}
variable {E' : BasicAtlas.OrderAction (IntegerRing K D) Y}

/-- Full-order commutation holds for the action of every element of the actual division
algebra in the whole rational atlas Hom. -/
theorem atlasRationalAction_commutes (z : BasicAtlas.OrderAction.RationalHom K E E' h) (d : D) :
    BasicAtlas.RationalHom.comp z.val (atlasRationalAction K D E d) =
      BasicAtlas.RationalHom.comp (atlasRationalAction K D E' d) z.val := by
  obtain ⟨t, rfl⟩ := (integerTensorEquiv K D).surjective d
  induction t using TensorProduct.inductionOn with
  | tmul c a =>
    rw [integerTensorEquiv_tmul, map_smul, map_smul,
      BasicAtlas.RationalHom.comp_smul, BasicAtlas.RationalHom.smul_comp,
      atlasRationalAction_coe, atlasRationalAction_coe]
    apply congrArg (fun z : BasicAtlas.RationalHom K X Y h => c • z)
    have : IsFractionRing 𝒪[K] K := (Valuation.integer.integers (valuation K)).isFractionRing
    have : Module.Flat 𝒪[K] K := IsLocalization.flat K (𝒪[K]⁰)
    apply BasicAtlas.RationalHom.ext_onCharts
    intro B b hb
    have hl := BasicAtlas.RationalHom.onChart_comp z.val
      (BasicAtlas.RationalHom.ofHom (E.endomorphism a)) B b hb
    have hr := BasicAtlas.RationalHom.onChart_comp
      (BasicAtlas.RationalHom.ofHom (E'.endomorphism a)) z.val B b hb
    have hE := BasicAtlas.RationalHom.onChart_ofHom (F := K) B (BasicAtlas.sourceChart h b) hb
      (E.endomorphism a)
    have hE' := BasicAtlas.RationalHom.onChart_ofHom (F := K) B b hb (E'.endomorphism a)
    exact hl.trans
      ((congrArg (ModuleLaw.RationalHom.comp (z.onChart B b hb).val) hE).trans
        ((z.commutes B b hb a).trans
          ((congrArg (fun x => ModuleLaw.RationalHom.comp x (z.onChart B b hb).val) hE'.symm).trans
            hr.symm)))
  | add x y hx hy =>
    rw [map_add, map_add, map_add, BasicAtlas.RationalHom.comp_add,
      BasicAtlas.RationalHom.add_comp, hx, hy]

end Equivariance

variable {K D}
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable {π : 𝒪[K]} {A : Nilp.{v, u} R (algebraMap 𝒪[K] R π)}
variable {Φ : SpecialModule.HeightSquaredModule (K := K) (D := D) (ι := ι) (R := κ) π}

section Transport

variable {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
variable {U U' V V' : SpecialAtlas K D ι S}
variable {e : U.atlas.opens = V.atlas.opens} {e' : U'.atlas.opens = V'.atlas.opens}

private def transportFraming (hs : U = U') (ht : V = V')
    (f : BasicAtlas.OrderAction.QuasiIsogeny K U.order V.order e) :
    BasicAtlas.OrderAction.QuasiIsogeny K U'.order V'.order e' := by
  subst U'
  subst V'
  exact f

private theorem transportFraming_hom (hs : U = U') (ht : V = V')
    (f : BasicAtlas.OrderAction.QuasiIsogeny K U.order V.order e) :
    HEq (transportFraming (e' := e') hs ht f).hom.val f.hom.val := by
  subst U'
  subst V'
  rfl

private theorem transportFraming_height (hs : U = U') (ht : V = V')
    (f : BasicAtlas.OrderAction.QuasiIsogeny K U.order V.order e) (π : 𝒪[K]) (q : ℕ) (n : ℤ) :
    (transportFraming (e' := e') hs ht f).hom.val.HasConstantChartHeight π q n ↔
      f.hom.val.HasConstantChartHeight π q n := by
  subst U'
  subst V'
  rfl

end Transport

namespace DrinfeldFramedAtlas

variable (X : DrinfeldFramedAtlas Φ A)
variable (g : GL (Fin (reducedDegree K D)) K × Dˣ)

/-- The actual shifted residue component in the source formula. -/
def actionResidueMap : κ →ₐ[𝒪[K]] ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj :=
  DrinfeldResidue.shift (DrinfeldAction.exponent K D g) X.residueMap

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
/-- The special target of the source formula is the original inverse-conjugated atlas. -/
def actionTarget : SpecialAtlas.HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := A.obj) π :=
  X.target.twistDivisionUnit g.2

/-- The new source is the fixed frame extended by the actual shifted residue map. -/
def actionSource : SpecialAtlas K D ι ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj :=
  SpecialAtlas.quotientFrame Φ.val (X.actionResidueMap g) X.target.val

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
/-- Reduction of the transformed target retains the same inverse-conjugated order action. -/
theorem actionTarget_reduction :
    (X.actionTarget g).val.reduction = X.target.val.reduction.twistDivisionUnit g.2 :=
  SpecialAtlas.twistDivisionUnit_baseChangeAlong X.target.val g.2 (Nilp.quotientO 𝒪[K] A)

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem actionTarget_opens : (X.actionTarget g).val.atlas.opens = X.target.val.atlas.opens := rfl

omit [Algebra 𝒪[K] R] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ] in
private theorem globalFrame_eq_of_opens_eq {S : Type u} [CommRing S] [Algebra 𝒪[K] S]
    (F : SpecialModule K D ι S) {a b : Set S} (h : a = b)
    (ha : Ideal.span a = ⊤) (hb : Ideal.span b = ⊤) :
    SpecialAtlas.ofGlobalCover F a ha = SpecialAtlas.ofGlobalCover F b hb := by
  subst b
  rfl

/-- The unchanged reduced cover gives exactly the extended frame on the transformed target. -/
theorem actionSource_eq :
    X.actionSource g = SpecialAtlas.quotientFrame Φ.val (X.actionResidueMap g) (X.actionTarget g).val := by
  unfold actionSource SpecialAtlas.quotientFrame
  apply globalFrame_eq_of_opens_eq
  rw [SpecialAtlas.reduction_opens, SpecialAtlas.reduction_opens, actionTarget_opens]

omit [Algebra 𝓀[K] κ] [Algebra.IsAlgebraic 𝓀[K] κ] [IsScalarTower 𝒪[K] 𝓀[K] κ] in
/-- The inverse division unit gives the actual reduced-target twist quasi-isogeny. -/
def actionTargetQuasiIsogeny : BasicAtlas.OrderAction.QuasiIsogeny K
    X.target.val.reduction.order (X.target.val.reduction.twistDivisionUnit g.2).order rfl :=
  X.target.val.reduction.twistDivisionUnitQuasiIsogeny g.2

variable (p : ℕ) [ExpChar κ p] {f : ℕ} (hcard : Nat.card 𝓀[K] = p ^ f)
variable (hFrob : ∀ j : ℕ, SpecialModule.RelativeFrobeniusQuasiIsogenyStatement Φ p (f * j))

/-- Signed Frobenius is restricted to the exact original reduced cover. -/
def actionSourceFrobenius : BasicAtlas.OrderAction.QuasiIsogeny K
    (X.actionSource g).order X.source.order rfl :=
  BasicAtlas.ofGlobalOrderQuasiIsogeny (DrinfeldResidue.signedFrameFrobenius Φ p hcard hFrob
    (DrinfeldAction.exponent K D g) (b := X.residueMap) rfl)
    X.target.val.reduction.atlas.opens X.target.val.reduction.atlas.covers

/-- The whole framing map specified by Drinfeld's formula, before proving its height. -/
def actionFramingOnCover (coordinates : Φ.val.MatrixCoordinates) :
    BasicAtlas.OrderAction.QuasiIsogeny K
      (X.actionSource g).order (X.target.val.reduction.twistDivisionUnit g.2).order rfl :=
  (((X.actionSourceFrobenius g p hcard hFrob).trans (X.matrixSourceQuasiIsogeny coordinates g.1⁻¹)).trans
    X.rho).trans (X.actionTargetQuasiIsogeny g)

set_option maxHeartbeats 1000000 in
/-- The whole underlying forward tensor is the source's ordered composition
of signed Frobenius, inverse division unit, inverse matrix and original framing. -/
theorem actionFramingOnCover_hom (coordinates : Φ.val.MatrixCoordinates) :
    (X.actionFramingOnCover g p hcard hFrob coordinates).hom.val =
      BasicAtlas.RationalHom.comp X.rho.hom.val
        (BasicAtlas.RationalHom.comp (X.matrixSourceQuasiIsogeny coordinates g.1⁻¹).hom.val
          (BasicAtlas.RationalHom.comp (atlasRationalAction K D X.source.order ((g.2⁻¹ : Dˣ) : D))
            (X.actionSourceFrobenius g p hcard hFrob).hom.val)) := by
  let d : D := (g.2⁻¹ : Dˣ)
  let r := X.rho.hom
  let m := (X.matrixSourceQuasiIsogeny coordinates g.1⁻¹).hom
  let t := (X.actionSourceFrobenius g p hcard hFrob).hom.val
  let sourceAction := atlasRationalAction K D X.source.order d
  let targetAction := atlasRationalAction K D X.target.val.reduction.order d
  change BasicAtlas.RationalHom.comp targetAction
      (BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp m.val t)) =
    BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp m.val
      (BasicAtlas.RationalHom.comp sourceAction t))
  calc
    _ = BasicAtlas.RationalHom.comp (BasicAtlas.RationalHom.comp targetAction r.val)
        (BasicAtlas.RationalHom.comp m.val t) := (BasicAtlas.RationalHom.comp_assoc _ _ _).symm
    _ = BasicAtlas.RationalHom.comp (BasicAtlas.RationalHom.comp r.val sourceAction)
        (BasicAtlas.RationalHom.comp m.val t) :=
      congrArg (fun q => BasicAtlas.RationalHom.comp q (BasicAtlas.RationalHom.comp m.val t))
        (atlasRationalAction_commutes K D r d).symm
    _ = BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp sourceAction
        (BasicAtlas.RationalHom.comp m.val t)) := BasicAtlas.RationalHom.comp_assoc _ _ _
    _ = BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp
        (BasicAtlas.RationalHom.comp sourceAction m.val) t) :=
      congrArg (BasicAtlas.RationalHom.comp r.val) (BasicAtlas.RationalHom.comp_assoc _ _ _).symm
    _ = BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp
        (BasicAtlas.RationalHom.comp m.val sourceAction) t) :=
      congrArg (fun q => BasicAtlas.RationalHom.comp r.val (BasicAtlas.RationalHom.comp q t))
        (atlasRationalAction_commutes K D m d).symm
    _ = _ := congrArg (BasicAtlas.RationalHom.comp r.val) (BasicAtlas.RationalHom.comp_assoc _ _ _)

set_option maxHeartbeats 1000000 in
/-- Evaluation on every test of the original reduced cover preserves all four
actual quasi-isogenies and their order of composition. -/
theorem actionFramingOnCover_onChart (coordinates : Φ.val.MatrixCoordinates)
    (B : CommAlgCat.{u} ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj)
    (b : X.target.val.reduction.atlas.opens)
    (hb : IsUnit (algebraMap
      ((Nilp.reductionFunctor R (algebraMap 𝒪[K] R π)).obj A).obj B b.val)) :
    (X.actionFramingOnCover g p hcard hFrob coordinates).onChart B b hb =
      ((((X.actionSourceFrobenius g p hcard hFrob).onChart B b hb).trans
        ((X.matrixSourceQuasiIsogeny coordinates g.1⁻¹).onChart B b hb)).trans
          (X.rho.onChart B b hb)).trans ((X.actionTargetQuasiIsogeny g).onChart B b hb) := by
  let frob := X.actionSourceFrobenius g p hcard hFrob
  let matrix := X.matrixSourceQuasiIsogeny coordinates g.1⁻¹
  let rho := X.rho
  let twist := X.actionTargetQuasiIsogeny g
  change (((frob.trans matrix).trans rho).trans twist).onChart B b hb = _
  calc
    _ = (((frob.trans matrix).trans rho).onChart B b hb).trans (twist.onChart B b hb) :=
      BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans ((frob.trans matrix).trans rho) twist B b hb
    _ = (((frob.trans matrix).onChart B b hb).trans (rho.onChart B b hb)).trans
        (twist.onChart B b hb) :=
      congrArg (fun z => z.trans (twist.onChart B b hb))
        (BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans (frob.trans matrix) rho B b hb)
    _ = _ := congrArg (fun z => (z.trans (rho.onChart B b hb)).trans (twist.onChart B b hb))
      (BasicAtlas.OrderAction.QuasiIsogeny.onChart_trans frob matrix B b hb)

set_option maxHeartbeats 1000000 in
/-- The same framing at the literal source and reduced target of the transformed triple. -/
def actionFraming (coordinates : Φ.val.MatrixCoordinates) :
    BasicAtlas.OrderAction.QuasiIsogeny K
      (SpecialAtlas.quotientFrame Φ.val (X.actionResidueMap g) (X.actionTarget g).val).order
      (X.actionTarget g).val.reduction.order rfl :=
  transportFraming (X.actionSource_eq g) (X.actionTarget_reduction g).symm
    (X.actionFramingOnCover g p hcard hFrob coordinates)

/-- Endpoint transport preserves the whole forward tensor in the printed order. -/
theorem actionFraming_hom (coordinates : Φ.val.MatrixCoordinates) :
    HEq (X.actionFraming g p hcard hFrob coordinates).hom.val
      (BasicAtlas.RationalHom.comp X.rho.hom.val
        (BasicAtlas.RationalHom.comp (X.matrixSourceQuasiIsogeny coordinates g.1⁻¹).hom.val
          (BasicAtlas.RationalHom.comp (atlasRationalAction K D X.source.order ((g.2⁻¹ : Dˣ) : D))
            (X.actionSourceFrobenius g p hcard hFrob).hom.val))) :=
  (transportFraming_hom (X.actionSource_eq g) (X.actionTarget_reduction g).symm
    (X.actionFramingOnCover g p hcard hFrob coordinates)).trans
      (heq_of_eq (X.actionFramingOnCover_hom g p hcard hFrob coordinates))

/-- The literal endpoint transport preserves the actual rank condition at any height. -/
theorem actionFraming_hasConstantChartHeight_iff (coordinates : Φ.val.MatrixCoordinates) (n : ℤ) :
    (X.actionFraming g p hcard hFrob coordinates).hom.val.HasConstantChartHeight π (Nat.card 𝓀[K]) n ↔
      (X.actionFramingOnCover g p hcard hFrob coordinates).hom.val.HasConstantChartHeight π
        (Nat.card 𝓀[K]) n :=
  transportFraming_height (X.actionSource_eq g) (X.actionTarget_reduction g).symm
    (X.actionFramingOnCover g p hcard hFrob coordinates) π (Nat.card 𝓀[K]) n

end DrinfeldFramedAtlas

end Langlands.FormalGroup.LocalDivision
