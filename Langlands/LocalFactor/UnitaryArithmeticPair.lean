import Langlands.Representation.Unitary.PositiveFormTensor
import Langlands.Weil.Representation.UnitaryRestriction
import Langlands.Automorphic.Unramified.RelativeWeilAssociation

/-!
# Unitarity of the actual arithmetic local pairs

The diagonal tensor form and restriction preserve the supplied positive forms.
The local results apply to every actual representative admitted by
`IsBaseRestriction`, including representatives in an independent universe.
-/

noncomputable section

universe uG uV uW u uP

namespace Langlands

namespace InvariantPositiveForm

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The external tensor form restricted to the diagonal group action. -/
def diagonalTensor (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ) :
    InvariantPositiveForm (ρ.tprod σ) where
  toInnerProductCore := (b.tensorProduct c).toInnerProductCore
  invariant g t s := (b.tensorProduct c).invariant (g, g) t s

@[simp]
theorem diagonalTensor_inner_tmul (b : InvariantPositiveForm ρ)
    (c : InvariantPositiveForm σ) (v v' : V) (w w' : W) :
    (b.diagonalTensor c).inner (v ⊗ₜ[ℂ] w) (v' ⊗ₜ[ℂ] w') =
      b.inner v v' * c.inner w w' :=
  b.tensorProduct_inner_tmul c v v' w w'

end InvariantPositiveForm

namespace FiniteRepresentation

variable {G : Type uG} [Group G]

/-- The actual diagonal tensor of two unitary finite representations is unitary. -/
theorem isUnitary_tensor
    {A : FiniteRepresentation.{0, uG, uV} ℂ G}
    {B : FiniteRepresentation.{0, uG, uW} ℂ G}
    (hA : A.IsUnitary) (hB : B.IsUnitary) : (tensor A B).IsUnitary := by
  obtain ⟨b⟩ := (isUnitary_iff_isUnitarizable A).mp hA
  obtain ⟨c⟩ := (isUnitary_iff_isUnitarizable B).mp hB
  exact (isUnitary_iff_isUnitarizable _).mpr ⟨b.diagonalTensor c⟩

end FiniteRepresentation

namespace WeilDeligneRepresentation

variable {G : Type uG} [Group G] {ν : G →* ℂˣ}

/-- Tensoring pairs preserves unitarity of their actual underlying Weil actions. -/
theorem tensor_isUnitary
    {A : WeilDeligneRepresentation.{0, uG, uV} ℂ G ν}
    {B : WeilDeligneRepresentation.{0, uG, uW} ℂ G ν}
    (hA : A.toFiniteRepresentation.IsUnitary) (hB : B.toFiniteRepresentation.IsUnitary) :
    (tensor A B).toFiniteRepresentation.IsUnitary :=
  FiniteRepresentation.isUnitary_tensor hA hB

end WeilDeligneRepresentation

namespace ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}} {v : FinitePlace F}

/-- Every actual local component of a unitary relative Weil representation is unitary. -/
theorem localComponent_isUnitary
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary) : (localComponent S ι).IsUnitary :=
  FiniteRepresentation.isUnitary_restrict ι.toMonoidHom hS

/-- Every bottom-field representative of the actual local pair class is unitary.
The representative's carrier universe is independent of that of `S`. -/
theorem isUnitary_of_isBaseRestriction_localPairClass
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {A : LocalFactor.CommonClosureWeilDeligne.Pair.{u, uP}
      (padicField v) (Correspondence.baseExtension (padicField v))}
    (hA : Correspondence.IsBaseRestriction (padicField v) (localPairClass S ι) A) :
    A.toFiniteRepresentation.IsUnitary := by
  obtain ⟨B, hB, ⟨e⟩⟩ := hA
  obtain ⟨f⟩ := (WeilDeligneRepresentation.classOf_eq_iff _ _).mp hB
  have hB' : B.toFiniteRepresentation.IsUnitary :=
    FiniteRepresentation.isUnitary_of_equiv f.representationEquiv
      (localComponent_isUnitary ι hS)
  exact FiniteRepresentation.isUnitary_of_equiv e.representationEquiv.symm
    (FiniteRepresentation.isUnitary_restrict _ hB')

/-- The same conclusion for the actual contragredient local pair class. -/
theorem isUnitary_of_isBaseRestriction_localPairClass_dual
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {A : LocalFactor.CommonClosureWeilDeligne.Pair.{u, uP}
      (padicField v) (Correspondence.baseExtension (padicField v))}
    (hA : Correspondence.IsBaseRestriction (padicField v)
      (localPairClass (FiniteRepresentation.dual S) ι) A) :
    A.toFiniteRepresentation.IsUnitary :=
  isUnitary_of_isBaseRestriction_localPairClass ι
    (FiniteRepresentation.isUnitary_dual S hS) hA

/-- The tensor used by the actual self-pair epsilon/gamma datum is unitary for
every admitted choice of the two bottom-field representatives. -/
theorem tensor_isUnitary_of_isBaseRestriction_localPairClass
    {S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (ι : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E)
    (hS : S.IsUnitary)
    {A B : LocalFactor.CommonClosureWeilDeligne.Pair.{u, uP}
      (padicField v) (Correspondence.baseExtension (padicField v))}
    (hA : Correspondence.IsBaseRestriction (padicField v) (localPairClass S ι) A)
    (hB : Correspondence.IsBaseRestriction (padicField v)
      (localPairClass (FiniteRepresentation.dual S) ι) B) :
    (WeilDeligneRepresentation.tensor A B).toFiniteRepresentation.IsUnitary :=
  WeilDeligneRepresentation.tensor_isUnitary
    (isUnitary_of_isBaseRestriction_localPairClass ι hS hA)
    (isUnitary_of_isBaseRestriction_localPairClass_dual ι hS hB)

end ClassField.Global.RelativeWeilGroup

end Langlands
