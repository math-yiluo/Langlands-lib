import Langlands.Geometry.FormalGroup.PolarizedFramedAffinePoints
import Langlands.Geometry.FormalGroup.RationalTorsionSimilitudeCoherence
import Langlands.Geometry.FormalGroup.RationalSectionIsoTransport

/-! # Base change of affine polarized framed triples -/

noncomputable section

universe u v w

namespace Langlands.FormalGroup.ModuleLaw.RationalSection

open TopologicalSpace _root_.AlgebraicGeometry

variable {O : Type u} [CommRing O]
variable {R : Type v} [CommRing R] [Algebra O R]
variable {F : Type v} [Field F] [Algebra O F]
variable {σ τ σ' τ' : Type} [Finite σ] [Finite τ] [Finite σ'] [Finite τ']
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}
variable {M' : ModuleLaw O R σ'} {N' : ModuleLaw O R τ'}

/-- Conjugation of an integral section is the section of the conjugated integral map. -/
theorem transportIso_ofHom (a : Iso M M') (b : Iso N N') (f : Hom M N)
    (U : Opens (PrimeSpectrum R)) :
    transportIso (F := F) a b U (ofHom f U) = ofHom (b.hom.comp (f.comp a.inv)) U := by
  change comp (ofHom b.hom U) (comp (ofHom f U) (ofHom a.inv U)) = _
  rw [comp_ofHom, comp_ofHom]

/-- Transport carries an integral commuting square to the specified integral arrow. -/
theorem transportIso_ofHom_of_commutes (a : Iso M M') (b : Iso N N')
    {f : Hom M N} {g : Hom M' N'} (h : b.hom.comp f = g.comp a.hom)
    (U : Opens (PrimeSpectrum R)) :
    transportIso (F := F) a b U (ofHom f U) = ofHom g U := by
  rw [transportIso_ofHom, ← Hom.comp_assoc, h, Hom.comp_assoc, a.hom_inv, Hom.comp_id]

end Langlands.FormalGroup.ModuleLaw.RationalSection

namespace Langlands.FormalGroup.PolarizedFramedAffinePoint

open CategoryTheory ModuleLaw Langlands.Shimura

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

variable {prime : ℕ} [Fact prime.Prime]
variable {W : Type} [CommRing W] [Algebra ℤ_[prime] W] {π : W}
variable {A : Type w} [Ring A] [Algebra ℤ_[prime] A] {star : AlgebraInvolution ℤ_[prime] A}
variable {frame : PolarizedOrderModule A star (ResidueRing W π) (prime : ℤ_[prime])}
variable {T U : Nilp.{0, 0} W π}

/-- The fixed residue coefficient map is natural on the actual Nilp reductions. -/
theorem frameCoefficientMap_natural (j : T ⟶ U) :
    (Nilp.reducedScalarMap ℤ_[prime] j).comp (frameCoefficientMap prime π T) =
      frameCoefficientMap prime π U := by
  apply AlgHom.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  change Nilp.reductionQuotient π U.obj (j.hom.hom (algebraMap W T.obj a)) =
    Nilp.reductionQuotient π U.obj (algebraMap W U.obj a)
  rw [j.hom.hom.commutes]

set_option maxHeartbeats 800000 in
/-- Compare the pulled-back frame with the frame over the new residue algebra. -/
def sourceComparison (j : T ⟶ U) :
    PolarizedOrderModule.Iso
      ((source (frame := frame) (T := T)).map (Nilp.reducedScalarMap ℤ_[prime] j))
      (source (frame := frame) (T := U)) :=
  (frame.mapSquareIso (frameCoefficientMap prime π T) (Nilp.reducedScalarMap ℤ_[prime] j)
    (frameCoefficientMap prime π U) (AlgHom.id ℤ_[prime] _)
    ((frameCoefficientMap_natural j).trans (AlgHom.id_comp _).symm)).trans
      ((source (frame := frame) (T := U)).mapIdIso)

set_option maxHeartbeats 800000 in
/-- Compare pullback of the reduced target with reduction of the pulled-back target. -/
def targetComparison (X : PolarizedFramedAffinePoint prime π frame T) (j : T ⟶ U) :
    PolarizedOrderModule.Iso (X.reducedTarget.map (Nilp.reducedScalarMap ℤ_[prime] j))
      ((X.target.map (Nilp.scalarMap ℤ_[prime] j)).map (Nilp.quotientO ℤ_[prime] U)) :=
  X.target.mapSquareIso (Nilp.quotientO ℤ_[prime] T) (Nilp.reducedScalarMap ℤ_[prime] j)
    (Nilp.scalarMap ℤ_[prime] j) (Nilp.quotientO ℤ_[prime] U) (Nilp.quotientO_natural _ j).symm

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Extend the polarized target and pull back the actual reduced framing. -/
def baseChange (X : PolarizedFramedAffinePoint prime π frame T) (j : T ⟶ U) :
    PolarizedFramedAffinePoint prime π frame U where
  target := X.target.map (Nilp.scalarMap ℤ_[prime] j)
  rho := RationalSection.transportIso (sourceComparison (frame := frame) j).orderIso.toModuleIso
    (X.targetComparison j).orderIso.toModuleIso ⊤
    (RationalSection.baseChange (Nilp.reducedScalarMap ℤ_[prime] j) ⊤ X.rho)
  commutes d := by
    let ψ := Nilp.reducedScalarMap ℤ_[prime] j
    let a := (sourceComparison (frame := frame) j).orderIso
    let b := (X.targetComparison j).orderIso
    have h := congrArg (RationalSection.baseChange ψ ⊤) (X.commutes d)
    simp only [RationalSection.baseChange_comp, RationalSection.baseChange_ofHom] at h
    change RationalSection.comp (RationalSection.baseChange ψ ⊤ X.rho)
        (RationalSection.ofHom ((source.map ψ).order.action d) ⊤) =
      RationalSection.comp (RationalSection.ofHom ((X.reducedTarget.map ψ).order.action d) ⊤)
        (RationalSection.baseChange ψ ⊤ X.rho) at h
    have ht := congrArg (RationalSection.transportIso a.toModuleIso b.toModuleIso ⊤) h
    rw [RationalSection.transportIso_comp a.toModuleIso a.toModuleIso b.toModuleIso,
      RationalSection.transportIso_comp a.toModuleIso b.toModuleIso b.toModuleIso] at ht
    rw [RationalSection.transportIso_ofHom_of_commutes a.toModuleIso a.toModuleIso
        (a.hom.commutes d),
      RationalSection.transportIso_ofHom_of_commutes b.toModuleIso b.toModuleIso
        (b.hom.commutes d)] at ht
    exact ht
  similitude := by
    obtain ⟨c, hc⟩ := X.similitude
    let a := sourceComparison (frame := frame) j
    let b := X.targetComparison j
    exact ⟨c, (hc.baseChange (Nilp.reducedScalarMap ℤ_[prime] j)).transportIso
      a.orderIso.toModuleIso b.orderIso.toModuleIso a.preserves b.preserves⟩

set_option maxHeartbeats 1500000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual isometries extending the framing square pull back along Nilp maps. -/
def Iso.baseChange {X Y : PolarizedFramedAffinePoint prime π frame T} (e : Iso X Y)
    (j : T ⟶ U) : Iso (X.baseChange j) (Y.baseChange j) where
  targetIso := e.targetIso.map (Nilp.scalarMap ℤ_[prime] j)
  square := by
    let φ := Nilp.scalarMap ℤ_[prime] j
    let ψ := Nilp.reducedScalarMap ℤ_[prime] j
    let a := (sourceComparison (frame := frame) j).orderIso.toModuleIso
    let b := (X.targetComparison j).orderIso.toModuleIso
    let c := (Y.targetComparison j).orderIso.toModuleIso
    let f := e.targetIso.orderIso.hom.val
    let f₁ := f.map (Nilp.quotientO ℤ_[prime] T)
    let f₂ := (f.map φ).map (Nilp.quotientO ℤ_[prime] U)
    have hn : c.hom.comp (f₁.map ψ) = f₂.comp b.hom :=
      (ModuleLaw.mapSquareIso_natural f (Nilp.quotientO ℤ_[prime] T) ψ φ
        (Nilp.quotientO ℤ_[prime] U) (Nilp.quotientO_natural _ j).symm).symm
    have h := congrArg (RationalSection.baseChange ψ ⊤) e.square
    change RationalSection.baseChange ψ ⊤
        (RationalSection.comp (RationalSection.ofHom f₁ ⊤) X.rho) =
      RationalSection.baseChange ψ ⊤ Y.rho at h
    rw [RationalSection.baseChange_comp, RationalSection.baseChange_ofHom] at h
    change RationalSection.comp (RationalSection.ofHom (f₁.map ψ) ⊤)
        (RationalSection.baseChange ψ ⊤ X.rho) = RationalSection.baseChange ψ ⊤ Y.rho at h
    have ht := congrArg (RationalSection.transportIso a c ⊤) h
    rw [RationalSection.transportIso_comp a b c,
      RationalSection.transportIso_ofHom_of_commutes b c hn] at ht
    exact ht

end Langlands.FormalGroup.PolarizedFramedAffinePoint
