import Langlands.Representation.Category.Contragredient
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Classification.SupercuspidalContragredientStatement

/-!
# The smooth contragredient of supercuspidal objects and classes

The bundled smooth contragredient restricted to actual supercuspidal objects
and their isomorphism classes, under two explicit hypotheses: compact open
subgroups are cofinal, and the smooth contragredient preserves the
supercuspidal condition (`SupercuspidalContragredientClosed`). Irreducibility
of the contragredient is the published irreducible admissible theory. For every
p-adic field the cofinality is `GeneralLinear.compactOpen_cofinal`, and the
closure follows from the proposition target
`GeneralLinear.SupercuspidalContragredientStatement`, which this module does
not prove.
-/

noncomputable section

open CategoryTheory

namespace Langlands

universe uF uV

namespace GeneralLinear

variable {F : Type uF} [Field F] {n : ℕ}

/-- A character of the determinant has an inverse that is again a character of
the determinant. -/
theorem ker_determinant_le_ker_inv {χ : GeneralLinear n F →* ℂˣ}
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker) :
    (determinant : GeneralLinear n F →* Fˣ).ker ≤ (χ⁻¹).ker := by
  intro g hg
  change (χ g)⁻¹ = 1
  rw [(χ.mem_ker).mp (hdet hg), inv_one]

variable [TopologicalSpace F] [IsTopologicalGroup (GeneralLinear n F)]

/-- The smooth contragredient of every supercuspidal smooth representation with
carrier in `Type uV` is supercuspidal. -/
def SupercuspidalContragredientClosed : Prop :=
  ∀ A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F),
    IsSupercuspidal A.representation →
      IsSupercuspidal (smoothContragredient A.representation)

namespace SupercuspidalRep

/-- The smooth contragredient of an actual supercuspidal object. -/
def contragredient (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ⟨A.obj.contragredient,
    (IrreducibleAdmissibleRep.contragredient hG A.toIrreducibleAdmissible).property.1,
    hsc A.obj A.property.2⟩

@[simp]
theorem contragredient_obj (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    (contragredient hG hsc A).obj = A.obj.contragredient := rfl

/-- The smooth contragredient restricted to the full supercuspidal subcategory. -/
def contragredientFunctor (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n)) :
    (SupercuspidalRep.{uF, uV} (F := F) (n := n))ᵒᵖ ⥤
      SupercuspidalRep.{uF, uV} (F := F) (n := n) :=
  ObjectProperty.lift _
    ((supercuspidalProperty (F := F) (n := n)).ι.op ⋙ SmoothRep.contragredientFunctor)
    (fun A => (contragredient hG hsc A.unop).property)

@[simp]
theorem contragredientFunctor_obj (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A : (SupercuspidalRep.{uF, uV} (F := F) (n := n))ᵒᵖ) :
    (contragredientFunctor hG hsc).obj A = contragredient hG hsc A.unop := rfl

/-- Isomorphic supercuspidal objects have isomorphic smooth contragredients. -/
def contragredientIso (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    {A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)} (e : A ≅ B) :
    contragredient hG hsc B ≅ contragredient hG hsc A :=
  (contragredientFunctor hG hsc).mapIso e.op

/-- The canonical evaluation isomorphism with the smooth bidual. -/
def bidualIso (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    A ≅ contragredient hG hsc (contragredient hG hsc A) :=
  isoMk (SmoothRep.bidualIso hG A.obj A.property.2.1)

/-- The smooth contragredient of the twist by a character of the determinant is
the twist of the smooth contragredient by the inverse character. -/
def contragredientTwistIso (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    contragredient hG hsc (twist χ hχ hdet A) ≅
      twist χ⁻¹ (isOpen_ker_inv hχ) (ker_determinant_le_ker_inv hdet)
        (contragredient hG hsc A) :=
  isoMk (SmoothRep.contragredientTwistIso χ hχ A.obj)

end SupercuspidalRep

namespace SupercuspidalClass

/-- The smooth contragredient on supercuspidal isomorphism classes. -/
def contragredient (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n)) :
    SupercuspidalClass.{uV, uF} (F := F) (n := n) →
      SupercuspidalClass.{uV, uF} (F := F) (n := n) :=
  Quotient.map (SupercuspidalRep.contragredient hG hsc)
    (fun _ _ ⟨e⟩ => ⟨(SupercuspidalRep.contragredientIso hG hsc e).symm⟩)

@[simp]
theorem contragredient_isoClass (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    contragredient hG hsc A.isoClass = (SupercuspidalRep.contragredient hG hsc A).isoClass :=
  rfl

/-- Forgetting supercuspidality commutes with the smooth contragredient. -/
theorem toSmoothDualClass_contragredient (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    (contragredient hG hsc a).toSmoothDualClass =
      SmoothDualClass.contragredient hG a.toSmoothDualClass := by
  induction a using Quotient.inductionOn with
  | h A => rfl

/-- The class of `B` is the contragredient of the class of `A` exactly when the
smooth contragredient of `A` is equivalent to `B`. -/
theorem contragredient_isoClass_eq_isoClass_iff (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (A B : SupercuspidalRep.{uF, uV} (F := F) (n := n)) :
    contragredient hG hsc A.isoClass = B.isoClass ↔
      Nonempty ((smoothContragredient A.obj.representation).Equiv
        B.obj.representation) := by
  rw [← toSmoothDualClass_injective.eq_iff, toSmoothDualClass_contragredient]
  exact SmoothDualClass.contragredient_mk_eq_mk_iff hG A.toIrreducibleAdmissible
    B.toIrreducibleAdmissible

/-- The smooth contragredient is an involution of the supercuspidal classes. -/
theorem contragredient_contragredient (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    contragredient hG hsc (contragredient hG hsc a) = a := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨(SupercuspidalRep.bidualIso hG hsc A).symm⟩

theorem contragredient_involutive (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n)) :
    Function.Involutive
      (contragredient hG hsc : SupercuspidalClass.{uV, uF} (F := F) (n := n) → _) :=
  contragredient_contragredient hG hsc

theorem contragredient_bijective (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n)) :
    Function.Bijective
      (contragredient hG hsc : SupercuspidalClass.{uV, uF} (F := F) (n := n) → _) :=
  (contragredient_involutive hG hsc).bijective

/-- Twisting by a character `χ` of the determinant and then dualizing equals
dualizing and then twisting by `χ⁻¹`. -/
theorem contragredient_twist (hG : CompactOpenCofinal (GeneralLinear n F))
    (hsc : SupercuspidalContragredientClosed.{uF, uV} (F := F) (n := n))
    (χ : GeneralLinear n F →* ℂˣ) (hχ : IsOpen (χ.ker : Set (GeneralLinear n F)))
    (hdet : (determinant : GeneralLinear n F →* Fˣ).ker ≤ χ.ker)
    (a : SupercuspidalClass.{uV, uF} (F := F) (n := n)) :
    contragredient hG hsc (twist χ hχ hdet a) =
      twist χ⁻¹ (isOpen_ker_inv hχ) (ker_determinant_le_ker_inv hdet)
        (contragredient hG hsc a) := by
  induction a using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨SupercuspidalRep.contragredientTwistIso hG hsc χ hχ hdet A⟩

end SupercuspidalClass

end GeneralLinear

namespace PadicField

variable {p : ℕ} [Fact p.Prime]

namespace TopologicalData

variable {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The proposition target `GeneralLinear.SupercuspidalContragredientStatement`
gives the closure hypothesis for every p-adic field, realization and rank. -/
theorem supercuspidalContragredientClosed
    (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}) (n : ℕ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    GeneralLinear.SupercuspidalContragredientClosed.{uF, uV} (F := F.Carrier) (n := n) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ := T.generalLinearTopologicalGroup n
  intro A hA
  exact (h p F T n _ A.representation A.isSmooth).1.mpr hA

/-- The smooth contragredient of supercuspidal classes for the topology of `T`,
given the proposition target `GeneralLinear.SupercuspidalContragredientStatement`. -/
def supercuspidalClassContragredient
    (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}) (n : ℕ) :
    letI := T.topology
    GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) →
      GeneralLinear.SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := n) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  GeneralLinear.SupercuspidalClass.contragredient (GeneralLinear.compactOpen_cofinal F T n)
    (T.supercuspidalContragredientClosed h n)

theorem supercuspidalClassContragredient_involutive
    (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}) (n : ℕ) :
    Function.Involutive (T.supercuspidalClassContragredient h n) := by
  let _ : TopologicalSpace F.Carrier := T.topology
  let _ := T.generalLinearTopologicalGroup n
  exact GeneralLinear.SupercuspidalClass.contragredient_involutive _ _

end TopologicalData

/-- The smooth contragredient on the canonical p-adic supercuspidal class space,
given the proposition target `GeneralLinear.SupercuspidalContragredientStatement`. -/
def SupercuspidalClass.contragredient {F : PadicField.{uF} p} {n : ℕ} {hn : 0 < n}
    (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}) :
    SupercuspidalClass.{uV, uF} F n hn → SupercuspidalClass.{uV, uF} F n hn :=
  F.canonicalTopologicalData.supercuspidalClassContragredient h n

theorem SupercuspidalClass.contragredient_involutive {F : PadicField.{uF} p} {n : ℕ}
    {hn : 0 < n} (h : GeneralLinear.SupercuspidalContragredientStatement.{uF, uV}) :
    Function.Involutive (SupercuspidalClass.contragredient (F := F) (hn := hn) h) :=
  F.canonicalTopologicalData.supercuspidalClassContragredient_involutive h n

end PadicField

end Langlands
