import Langlands.VirtualRepresentation.Supercuspidal.FieldTransport
import Langlands.VirtualRepresentation.Supercuspidal.Contragredient
import Langlands.VirtualRepresentation.Supercuspidal.UnitaryTwist
import Langlands.Representation.Aubert.General.ContragredientTransport

/-!
# Field transport commutes with contragredients and determinant twists

For a field isomorphism `σ : F ≃+* E` that is a homeomorphism, pulling
supercuspidal representations of `GL_n(E)` back to `GL_n(F)` along the entrywise
isomorphism commutes with the smooth contragredient, and carries the twist by a
character `χE` of `GL_n(E)` to the twist by `χF = χE ∘ σ`. The determinant of
the transported matrix is the image of the determinant. These statements hold
for representatives, classes and the integral lattices; for p-adic fields they
also hold on the unitary lattices with the canonical contragredient.
-/

noncomputable section

open CategoryTheory

universe uF uE uV

namespace Langlands.VirtualRepresentation

/-- Relabelling along two commuting squares of basis bijections gives the same
lattice map. -/
theorem reindex_reindex_of_comm_basis {ι κ μ ν : Type*} (σ : ι ≃ κ) (τ : κ ≃ μ)
    (τ' : ι ≃ ν) (σ' : ν ≃ μ) (h : ∀ i, τ (σ i) = σ' (τ' i)) (x : IntegralLattice ι) :
    reindex τ (reindex σ x) = reindex σ' (reindex τ' x) := by
  have hst : σ.trans τ = τ'.trans σ' := Equiv.ext h
  change ((reindex σ).trans (reindex τ)) x = ((reindex τ').trans (reindex σ')) x
  simp only [reindex, Finsupp.domLCongr_trans, hst]

end Langlands.VirtualRepresentation

namespace Langlands.GeneralLinear

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  {n : ℕ} (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)

/-- The determinant of the entrywise transport is the transport of the determinant. -/
theorem determinant_fieldEquiv (g : GeneralLinear n F) :
    ((determinant (fieldEquiv n σ hσ hσs g) : Eˣ) : E) = σ ((determinant g : Fˣ) : F) := by
  change (σ.toRingHom.mapMatrix (g : Matrix (Fin n) (Fin n) F)).det =
    σ.toRingHom (g : Matrix (Fin n) (Fin n) F).det
  rw [RingHom.map_det]

namespace SupercuspidalRep

/-- Pullback along `σ` carries the twist by `χE` to the twist by `χF = χE ∘ σ`,
through the identity map of the common space. -/
def fieldPullbackTwistIso (χE : GeneralLinear n E →* ℂˣ)
    (hχE : IsOpen (χE.ker : Set (GeneralLinear n E)))
    (hdetE : (determinant : GeneralLinear n E →* Eˣ).ker ≤ χE.ker)
    (χF : GeneralLinear n F →* ℂˣ) (hχF : IsOpen (χF.ker : Set (GeneralLinear n F)))
    (hdetF : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χF.ker)
    (hχ : ∀ g, χF g = χE (fieldEquiv n σ hσ hσs g))
    (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) (twist χE hχE hdetE A) ≅
      twist χF hχF hdetF (fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A) :=
  ObjectProperty.isoMk _ (SmoothRep.mkIso
    (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) (fun g => by
      ext v
      change (χE (fieldEquiv n σ hσ hσs g) : ℂ) •
          A.obj.representation (fieldEquiv n σ hσ hσs g) v =
        (χF g : ℂ) • A.obj.representation (fieldEquiv n σ hσ hσs g) v
      rw [hχ])))

variable [IsTopologicalGroup (GeneralLinear n F)] [IsTopologicalGroup (GeneralLinear n E)]
  (hGF : CompactOpenCofinal (GeneralLinear n F))
  (hscF : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
  (hGE : CompactOpenCofinal (GeneralLinear n E))
  (hscE : SupercuspidalContragredientClosed.{uE, uV} (F := E) (n := n))

/-- Pullback along `σ` commutes with the smooth contragredient: both are the
same smooth linear functionals. -/
def fieldPullbackContragredientIso (A : SupercuspidalRep.{uE, uV} (F := E) (n := n)) :
    fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) (contragredient hGE hscE A) ≅
      contragredient hGF hscF (fieldPullback (σ := σ) (hσ := hσ) (hσs := hσs) A) :=
  ObjectProperty.isoMk _
    (Aubert.General.contragredientPullbackIso (fieldEquiv n σ hσ hσs) A.obj).symm

end SupercuspidalRep

namespace SupercuspidalClass

/-- On classes, pullback along `σ` carries the twist by `χE` to the twist by
`χF = χE ∘ σ`. -/
theorem fieldPullback_twist (χE : GeneralLinear n E →* ℂˣ)
    (hχE : IsOpen (χE.ker : Set (GeneralLinear n E)))
    (hdetE : (determinant : GeneralLinear n E →* Eˣ).ker ≤ χE.ker)
    (χF : GeneralLinear n F →* ℂˣ) (hχF : IsOpen (χF.ker : Set (GeneralLinear n F)))
    (hdetF : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χF.ker)
    (hχ : ∀ g, χF g = χE (fieldEquiv n σ hσ hσs g))
    (a : SupercuspidalClass.{uV, uE} (F := E) (n := n)) :
    fieldPullback σ hσ hσs (twist χE hχE hdetE a) =
      twist χF hχF hdetF (fieldPullback σ hσ hσs a) := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound
      ⟨SupercuspidalRep.fieldPullbackTwistIso σ hσ hσs χE hχE hdetE χF hχF hdetF hχ A⟩

variable [IsTopologicalGroup (GeneralLinear n F)] [IsTopologicalGroup (GeneralLinear n E)]
  (hGF : CompactOpenCofinal (GeneralLinear n F))
  (hscF : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
  (hGE : CompactOpenCofinal (GeneralLinear n E))
  (hscE : SupercuspidalContragredientClosed.{uE, uV} (F := E) (n := n))

/-- On classes, pullback along `σ` commutes with the smooth contragredient. -/
theorem fieldPullback_contragredient (a : SupercuspidalClass.{uV, uE} (F := E) (n := n)) :
    fieldPullback σ hσ hσs (contragredient hGE hscE a) =
      contragredient hGF hscF (fieldPullback σ hσ hσs a) := by
  induction a using Quotient.inductionOn with
  | h A =>
    exact Quotient.sound
      ⟨SupercuspidalRep.fieldPullbackContragredientIso σ hσ hσs hGF hscF hGE hscE A⟩

end SupercuspidalClass

end Langlands.GeneralLinear

namespace Langlands.VirtualRepresentation.Supercuspidal

open GeneralLinear

variable {F : Type uF} {E : Type uE} [Field F] [Field E]
  [TopologicalSpace F] [TopologicalSpace E]
  (σ : F ≃+* E) (hσ : Continuous σ) (hσs : Continuous σ.symm)

section Twist

variable (χE : ∀ n : ℕ+, GeneralLinear (n : ℕ) E →* ℂˣ)
  (hχE : ∀ n : ℕ+, IsOpen ((χE n).ker : Set (GeneralLinear (n : ℕ) E)))
  (hdetE : ∀ n : ℕ+, (determinant : GeneralLinear (n : ℕ) E →* Eˣ).ker ≤ (χE n).ker)
  (χF : ∀ n : ℕ+, GeneralLinear (n : ℕ) F →* ℂˣ)
  (hχF : ∀ n : ℕ+, IsOpen ((χF n).ker : Set (GeneralLinear (n : ℕ) F)))
  (hdetF : ∀ n : ℕ+, (determinant : GeneralLinear (n : ℕ) F →* Fˣ).ker ≤ (χF n).ker)
  (hχ : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), χF n g = χE n (fieldEquiv n σ hσ hσs g))

include hχ in
/-- Pullback along `σ` carries the twist by `χE` to the twist by `χF = χE ∘ σ`
on the supercuspidal basis. -/
theorem fieldBasisEquiv_twistBasisEquiv (b : Basis.{uE, uV} E) :
    fieldBasisEquiv σ hσ hσs (twistBasisEquiv χE hχE hdetE b) =
      twistBasisEquiv χF hχF hdetF (fieldBasisEquiv σ hσ hσs b) := by
  rcases b with ⟨n, a⟩
  exact congrArg (Sigma.mk n) (SupercuspidalClass.fieldPullback_twist σ hσ hσs
    (χE n) (hχE n) (hdetE n) (χF n) (hχF n) (hdetF n) (hχ n) a)

include hχ in
/-- The same compatibility on the unitary supercuspidal basis. -/
theorem fieldUnitaryBasisEquiv_unitaryTwistBasisEquiv
    (huE : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) E), ‖(χE n g : ℂ)‖ = 1)
    (huF : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(χF n g : ℂ)‖ = 1)
    (b : UnitaryBasis.{uE, uV} E) :
    fieldUnitaryBasisEquiv σ hσ hσs (unitaryTwistBasisEquiv χE hχE hdetE huE b) =
      unitaryTwistBasisEquiv χF hχF hdetF huF (fieldUnitaryBasisEquiv σ hσ hσs b) :=
  Subtype.ext (fieldBasisEquiv_twistBasisEquiv σ hσ hσs χE hχE hdetE χF hχF hdetF hχ b.val)

include hχ in
/-- Pullback along `σ` carries the unitary lattice twist by `χE` to the twist by
`χF = χE ∘ σ`. -/
theorem fieldUnitaryLatticeEquiv_unitaryTwistLatticeEquiv
    (huE : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) E), ‖(χE n g : ℂ)‖ = 1)
    (huF : ∀ (n : ℕ+) (g : GeneralLinear (n : ℕ) F), ‖(χF n g : ℂ)‖ = 1)
    (x : UnitaryLattice.{uE, uV} E) :
    fieldUnitaryLatticeEquiv σ hσ hσs (unitaryTwistLatticeEquiv χE hχE hdetE huE x) =
      unitaryTwistLatticeEquiv χF hχF hdetF huF (fieldUnitaryLatticeEquiv σ hσ hσs x) :=
  reindex_reindex_of_comm_basis _ _ _ _
    (fieldUnitaryBasisEquiv_unitaryTwistBasisEquiv σ hσ hσs χE hχE hdetE χF hχF hdetF hχ
      huE huF) x

end Twist

section Dual

variable [∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F)]
  [∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) E)]
  (hGF : ∀ n : ℕ+, CompactOpenCofinal (GeneralLinear (n : ℕ) F))
  (hscF : ∀ n : ℕ+, SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := (n : ℕ)))
  (hGE : ∀ n : ℕ+, CompactOpenCofinal (GeneralLinear (n : ℕ) E))
  (hscE : ∀ n : ℕ+, SupercuspidalContragredientClosed.{uE, uV} (F := E) (n := (n : ℕ)))

/-- Pullback along `σ` commutes with the smooth contragredient on the
supercuspidal basis. -/
theorem fieldBasisEquiv_dualBasisEquiv (b : Basis.{uE, uV} E) :
    fieldBasisEquiv σ hσ hσs (dualBasisEquiv hGE hscE b) =
      dualBasisEquiv hGF hscF (fieldBasisEquiv σ hσ hσs b) := by
  rcases b with ⟨n, a⟩
  exact congrArg (Sigma.mk n) (SupercuspidalClass.fieldPullback_contragredient σ hσ hσs
    (hGF n) (hscF n) (hGE n) (hscE n) a)

end Dual

end Langlands.VirtualRepresentation.Supercuspidal

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (E : PadicField.{uE} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- Pullback along an isomorphism of p-adic fields commutes with the canonical
smooth contragredient on the unitary supercuspidal basis. -/
theorem unitaryBasisEquiv_unitaryContragredientBasisEquiv (b : UnitaryBasis.{uE, uV} E) :
    unitaryBasisEquiv F E f (unitaryContragredientBasisEquiv E b) =
      unitaryContragredientBasisEquiv F (unitaryBasisEquiv F E f b) := by
  let := F.canonicalTopologicalData.topology
  let := E.canonicalTopologicalData.topology
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) F.Carrier) :=
    fun n => F.canonicalTopologicalData.generalLinearTopologicalGroup n
  let : ∀ n : ℕ+, IsTopologicalGroup (GeneralLinear (n : ℕ) E.Carrier) :=
    fun n => E.canonicalTopologicalData.generalLinearTopologicalGroup n
  exact Subtype.ext (Supercuspidal.fieldBasisEquiv_dualBasisEquiv f.toRingEquiv
    (continuous_algEquiv F E f) (continuous_algEquiv E F f.symm)
    (fun n => GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n)
    (fun n => F.canonicalTopologicalData.supercuspidalContragredientClosed
      GeneralLinear.supercuspidalContragredient n)
    (fun n => GeneralLinear.compactOpen_cofinal E E.canonicalTopologicalData n)
    (fun n => E.canonicalTopologicalData.supercuspidalContragredientClosed
      GeneralLinear.supercuspidalContragredient n) b.val)

/-- Pullback along an isomorphism of p-adic fields commutes with the canonical
smooth contragredient on the unitary supercuspidal lattices. -/
theorem unitaryLatticeEquiv_unitaryContragredientLatticeEquiv
    (x : UnitaryLattice.{uE, uV} E) :
    unitaryLatticeEquiv F E f (unitaryContragredientLatticeEquiv E x) =
      unitaryContragredientLatticeEquiv F (unitaryLatticeEquiv F E f x) :=
  reindex_reindex_of_comm_basis _ _ _ _
    (unitaryBasisEquiv_unitaryContragredientBasisEquiv F E f) x

end Langlands.VirtualRepresentation.PadicSupercuspidal
