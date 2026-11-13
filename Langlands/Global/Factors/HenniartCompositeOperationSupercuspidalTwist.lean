import Langlands.VirtualRepresentation.Supercuspidal.FieldTransportOperations
import Langlands.Global.Factors.HenniartCompositeMapStatement

/-!
# Field transport of supercuspidal twists and `GL₁` classes

For an isomorphism `f : F ≅ E` of p-adic fields and modulus-one field characters
`χE` of `E` and `χF` of `F` with `χE ∘ f = χF`, pullback of unitary supercuspidal
classes along `f` carries the twist by `χE ∘ det` to the twist by `χF ∘ det`, and
the `GL₁` class of `χE` to the `GL₁` class of `χF`.

The completion form applies this to `f : K ≅ F_v` and the pullback
`completionSupercuspidalLatticeEquiv v h K f` used by Henniart's composite map.
-/

noncomputable section

open CategoryTheory

universe u uF uE uK uV

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- Pullback along `f : F ≅ E` carries the unitary twist by `χE ∘ det` to the
unitary twist by `χF ∘ det` when `χE ∘ f = χF`. -/
theorem unitaryLatticeEquiv_unitaryCharacterTwistLatticeEquiv
    (χE : Correspondence.QuasiCharacter E) (hχE : ∀ b, ‖(χE b : ℂ)‖ = 1)
    (χF : Correspondence.QuasiCharacter F) (hχF : ∀ a, ‖(χF a : ℂ)‖ = 1)
    (hrel : ∀ (a : F.Carrierˣ) (b : E.Carrierˣ),
      (b : E.Carrier) = f (a : F.Carrier) → χE b = χF a)
    (x : UnitaryLattice.{uE, uV} E) :
    unitaryLatticeEquiv F E f (unitaryCharacterTwistLatticeEquiv E χE hχE x) =
      unitaryCharacterTwistLatticeEquiv F χF hχF (unitaryLatticeEquiv F E f x) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  exact Supercuspidal.fieldUnitaryLatticeEquiv_unitaryTwistLatticeEquiv f.toRingEquiv
    (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm)
    (fun n => Correspondence.determinantQuasiCharacter E n χE)
    (fun n => Correspondence.isOpen_ker_determinantQuasiCharacter E n χE)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χE.toMonoidHom)
    (fun n => Correspondence.determinantQuasiCharacter F n χF)
    (fun n => Correspondence.isOpen_ker_determinantQuasiCharacter F n χF)
    (fun _ => GeneralLinear.ker_determinant_le_ker_comp χF.toMonoidHom)
    (fun _ g => (hrel _ _ (GeneralLinear.determinant_fieldEquiv f.toRingEquiv
      (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) g)).symm)
    (fun _ _ => hχE _) (fun _ _ => hχF _) x

/-- Pullback along `f : F ≅ E` of the `GL₁` representative of `χE` is the `GL₁`
representative of `χF` when `χE ∘ f = χF`, through the identity of the common
line. -/
def rankOneSupercuspidalObjectFieldPullbackIso
    (χE : Correspondence.QuasiCharacter E) (χF : Correspondence.QuasiCharacter F)
    (hrel : ∀ (a : F.Carrierˣ) (b : E.Carrierˣ),
      (b : E.Carrier) = f (a : F.Carrier) → χE b = χF a) :
    letI := F.canonicalTopologicalData.topology
    letI := E.canonicalTopologicalData.topology
    GeneralLinear.SupercuspidalRep.fieldPullback (σ := f.toRingEquiv)
        (hσ := continuous_algEquiv F E f) (hσs := continuous_algEquiv E F f.symm)
        (Correspondence.rankOneSupercuspidalObject.{uE, uV} E χE) ≅
      Correspondence.rankOneSupercuspidalObject.{uF, uV} F χF :=
  letI := F.canonicalTopologicalData.topology
  letI := E.canonicalTopologicalData.topology
  ObjectProperty.isoMk _ (SmoothRep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℂ (ULift.{uV} ℂ)) (fun g => by
      have hg : Correspondence.determinantQuasiCharacter E 1 χE
          (GeneralLinear.fieldEquiv 1 f.toRingEquiv (continuous_algEquiv F E f)
            (continuous_algEquiv E F f.symm) g) =
          Correspondence.determinantQuasiCharacter F 1 χF g :=
        hrel _ _ (GeneralLinear.determinant_fieldEquiv f.toRingEquiv
          (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) g)
      ext v
      change ((Correspondence.determinantQuasiCharacter E 1 χE
          (GeneralLinear.fieldEquiv 1 f.toRingEquiv (continuous_algEquiv F E f)
            (continuous_algEquiv E F f.symm) g) : ℂˣ) : ℂ) • (v : ULift.{uV} ℂ) =
        ((Correspondence.determinantQuasiCharacter F 1 χF g : ℂˣ) : ℂ) • v
      rw [hg])))

/-- Pullback along `f : F ≅ E` carries the `GL₁` class of `χE` to the `GL₁` class
of `χF` when `χE ∘ f = χF`. -/
theorem includeUnitary_unitaryLatticeEquiv_rankOne
    (χE : Correspondence.QuasiCharacter E) (χF : Correspondence.QuasiCharacter F)
    (hrel : ∀ (a : F.Carrierˣ) (b : E.Carrierˣ),
      (b : E.Carrier) = f (a : F.Carrier) → χE b = χF a)
    (y : UnitaryLattice.{uE, uV} E)
    (hy : includeUnitary E y =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uE, uV} E χE⟩ :
        Basis.{uE, uV} E)) :
    includeUnitary F (unitaryLatticeEquiv F E f y) =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uF, uV} F χF⟩ :
        Basis.{uF, uV} F) := by
  rw [includeUnitary_unitaryLatticeEquiv, hy]
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  refine (Supercuspidal.fieldLatticeEquiv_generator f.toRingEquiv
    (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm) _).trans ?_
  congr 1
  refine Sigma.ext rfl (heq_of_eq ?_)
  exact Quotient.sound ⟨rankOneSupercuspidalObjectFieldPullbackIso F E f χE χF hrel⟩

end Langlands.VirtualRepresentation.PadicSupercuspidal

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- Pullback along `completionSupercuspidalLatticeEquiv` carries the twist by
`χ' ∘ det` to the twist by `χ ∘ det` when `χ' ∘ f = χ`. -/
theorem completionSupercuspidalLatticeEquiv_unitaryCharacterTwistLatticeEquiv
    (χ : Correspondence.QuasiCharacter K) (hχ : ∀ a, ‖(χ a : ℂ)‖ = 1)
    (χ' : Correspondence.QuasiCharacter (padicField v)) (hχ' : ∀ b, ‖(χ' b : ℂ)‖ = 1)
    (hrel : letI := (padicFieldAt v h).algebra
      ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
        (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a)
    (y : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v)) :
    completionSupercuspidalLatticeEquiv v h K f
        (PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv (padicField v) χ' hχ' y) =
      PadicSupercuspidal.unitaryCharacterTwistLatticeEquiv K χ hχ
        (completionSupercuspidalLatticeEquiv v h K f y) := by
  subst h
  exact PadicSupercuspidal.unitaryLatticeEquiv_unitaryCharacterTwistLatticeEquiv
    K (padicFieldAt v rfl) f χ' hχ' χ hχ hrel y

/-- Pullback along `completionSupercuspidalLatticeEquiv` carries the `GL₁` class
of `χ'` to the `GL₁` class of `χ` when `χ' ∘ f = χ`. -/
theorem includeUnitary_completionSupercuspidalLatticeEquiv_rankOne
    (χ : Correspondence.QuasiCharacter K)
    (χ' : Correspondence.QuasiCharacter (padicField v))
    (hrel : letI := (padicFieldAt v h).algebra
      ∀ (a : K.Carrierˣ) (b : (padicField v).Carrierˣ),
        (b : (padicField v).Carrier) = f (a : K.Carrier) → χ' b = χ a)
    (y : PadicSupercuspidal.UnitaryLattice.{u, uV} (padicField v))
    (hy : PadicSupercuspidal.includeUnitary (padicField v) y =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{u, uV} (padicField v) χ'⟩ :
        PadicSupercuspidal.Basis.{u, uV} (padicField v))) :
    PadicSupercuspidal.includeUnitary K (completionSupercuspidalLatticeEquiv v h K f y) =
      generator (⟨1, Correspondence.rankOneSupercuspidalClass.{uK, uV} K χ⟩ :
        PadicSupercuspidal.Basis.{uK, uV} K) := by
  subst h
  exact PadicSupercuspidal.includeUnitary_unitaryLatticeEquiv_rankOne
    K (padicFieldAt v rfl) f χ' χ hrel y hy

end Langlands.Global
