import Langlands.Geometry.FormalGroup.DivisionOrder
import Langlands.Geometry.FormalGroup.TangentCharacters
import Langlands.Geometry.FormalGroup.IsogenyBaseChange
import Langlands.Algebra.LocalDivisionReducedDegree
import Mathlib.RingTheory.Etale.Basic

/-! # Special finite-coordinate formal modules over the actual division order -/

noncomputable section

universe u v w s

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L]
  (ι : L →ₐ[K] D)

/-- The actual integer ring in an embedded field, with the restricted division valuation. -/
abbrev SubfieldIntegerRing := (localDivisionSubfieldValuation K D ι).integer

/-- The original integral scalar map equips the embedded integer ring with its O-algebra. -/
instance subfieldIntegerAlgebra : Algebra 𝒪[K] (SubfieldIntegerRing K D ι) :=
  (localDivisionSubfieldBaseIntegerMap K D ι).toAlgebra

/-- Inclusion of the embedded integer ring into the actual division order respects scalars. -/
def subfieldIntegerInclusion : SubfieldIntegerRing K D ι →ₐ[𝒪[K]] IntegerRing K D where
  __ := localDivisionSubfieldIntegerMap K D ι
  commutes' a := by
    apply Subtype.ext
    exact ι.commutes (a : K)

@[simp]
theorem subfieldIntegerInclusion_coe (a : SubfieldIntegerRing K D ι) :
    (subfieldIntegerInclusion K D ι a : D) = ι (a : L) := rfl

/-- An actual embedded integer ring is finite etale over O and its fraction field
has the full reduced degree. No existence of such an embedding is assumed globally. -/
def IsUnramifiedSubfieldOfReducedDegree : Prop :=
  FiniteDimensional K L ∧ Module.Finite 𝒪[K] (SubfieldIntegerRing K D ι) ∧
    Algebra.Etale 𝒪[K] (SubfieldIntegerRing K D ι) ∧
      Module.finrank K L = CentralSimple.reducedDegree K D

variable (R : Type v) [CommRing R] [Algebra 𝒪[K] R]

/-- A special coordinate formal module relative to an actual unramified
integer subfield, with the source's distinct-character condition on every geometric fibre. -/
structure SpecialModule where
  formalModule : ModuleLaw 𝒪[K] R (Fin (CentralSimple.reducedDegree K D))
  order : ModuleLaw.OrderAction (IntegerRing K D) formalModule
  unramified : IsUnramifiedSubfieldOfReducedDegree K D ι
  tangent : order.HasGeometricTangentCharacters.{u, u, v, max u v, s}
    (subfieldIntegerInclusion K D ι).toRingHom (CentralSimple.reducedDegree K D)

namespace SpecialModule

variable {K D ι R}
variable {S : Type w} [CommRing S] [Algebra 𝒪[K] S]
  (X Y Z : SpecialModule K D ι R)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [FiniteDimensional K D] [Algebra.IsCentral K D] in
/-- The coordinate tangent space has the source's prescribed dimension. -/
theorem tangent_finrank (κ : Type*) [Field κ] :
    Module.finrank κ (Fin (CentralSimple.reducedDegree K D) → κ) =
      CentralSimple.reducedDegree K D :=
  Module.finrank_fin_fun κ

/-- Height d² uses the actual residue cardinality and actual scalar-kernel ranks. -/
def HasHeightSquared (π : 𝒪[K]) : Prop :=
  Irreducible π ∧ X.formalModule.HasPiHeight π (Nat.card 𝓀[K])
    ((CentralSimple.reducedDegree K D) ^ 2)

/-- Isomorphisms are actual order-linear formal isomorphisms. -/
abbrev Iso := ModuleLaw.OrderAction.Iso X.order Y.order

namespace Iso

/-- Identity order-linear isomorphism of a special coordinate module. -/
def refl : Iso X X where
  hom := ModuleLaw.OrderAction.Hom.id X.order
  inv := ModuleLaw.OrderAction.Hom.id X.order
  inv_hom := by apply Subtype.ext; exact ModuleLaw.Hom.id_comp _
  hom_inv := by apply Subtype.ext; exact ModuleLaw.Hom.id_comp _

variable {X Y Z}

/-- Reverse the two actual inverse maps. -/
def symm (f : Iso X Y) : Iso Y X :=
  ⟨f.inv, f.hom, f.hom_inv, f.inv_hom⟩

/-- Compose the actual order-linear maps and reverse the inverse maps. -/
def trans (f : Iso X Y) (g : Iso Y Z) : Iso X Z where
  hom := g.hom.comp f.hom
  inv := f.inv.comp g.inv
  inv_hom := by
    apply Subtype.ext
    change (f.inv.val.comp g.inv.val).comp (g.hom.val.comp f.hom.val) =
      ModuleLaw.Hom.id X.formalModule
    have hg := congrArg Subtype.val g.inv_hom
    have hf := congrArg Subtype.val f.inv_hom
    change g.inv.val.comp g.hom.val = ModuleLaw.Hom.id Y.formalModule at hg
    change f.inv.val.comp f.hom.val = ModuleLaw.Hom.id X.formalModule at hf
    rw [ModuleLaw.Hom.comp_assoc, ← ModuleLaw.Hom.comp_assoc g.inv.val,
      hg, ModuleLaw.Hom.id_comp, hf]
  hom_inv := by
    apply Subtype.ext
    change (g.hom.val.comp f.hom.val).comp (f.inv.val.comp g.inv.val) =
      ModuleLaw.Hom.id Z.formalModule
    have hf := congrArg Subtype.val f.hom_inv
    have hg := congrArg Subtype.val g.hom_inv
    change f.hom.val.comp f.inv.val = ModuleLaw.Hom.id Y.formalModule at hf
    change g.hom.val.comp g.inv.val = ModuleLaw.Hom.id Z.formalModule at hg
    rw [ModuleLaw.Hom.comp_assoc, ← ModuleLaw.Hom.comp_assoc f.hom.val,
      hf, ModuleLaw.Hom.id_comp, hg]

/-- Height is preserved by an actual order-linear isomorphism. -/
theorem hasHeightSquared_iff (f : Iso X Y) (π : 𝒪[K]) :
    X.HasHeightSquared π ↔ Y.HasHeightSquared π := by
  exact and_congr Iff.rfl
    (f.toModuleIso.hasPiHeight_iff π (Nat.card 𝓀[K]) _)

end Iso

/-- Actual formal isomorphism is the equivalence relation used for coordinate classes. -/
def isoSetoid : Setoid (SpecialModule K D ι R) where
  r X Y := Nonempty (Iso X Y)
  iseqv := ⟨fun X => ⟨Iso.refl X⟩,
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- Coefficient extension preserves the special character condition when the test-field
universe is unchanged. Height preservation is supplied separately by finite-kernel base change. -/
def mapSameUniverse {S : Type v} [CommRing S] [Algebra 𝒪[K] S] (θ : R →ₐ[𝒪[K]] S) :
    SpecialModule K D ι S where
  formalModule := X.formalModule.map θ
  order := X.order.map θ
  unramified := X.unramified
  tangent := X.tangent.map θ

/-- Tensor base change preserves all scalar-kernel ranks in the height certificate. -/
theorem HasHeightSquared.map {X : SpecialModule K D ι R} {π : 𝒪[K]}
    (h : X.HasHeightSquared π) {S : Type v} [CommRing S] [Algebra 𝒪[K] S]
    (θ : R →ₐ[𝒪[K]] S) : (X.mapSameUniverse θ).HasHeightSquared π :=
  ⟨h.1, h.2.map θ⟩

/-- The height condition includes nilpotence of the actual image of the uniformizer. -/
theorem base_nilpotent {π : 𝒪[K]} (h : X.HasHeightSquared π) :
    IsNilpotent (algebraMap 𝒪[K] R π) := h.2.piDivisible.base_nilpotent

/-- Every scalar-power kernel has the actual constant rank q^(n*d²). -/
theorem scalarPower_rank {π : 𝒪[K]} (h : X.HasHeightSquared π) (n : ℕ) :
    (X.formalModule.scalarHom (π ^ n)).HasKernelRank
      ((Nat.card 𝓀[K]) ^ (n * (CentralSimple.reducedDegree K D) ^ 2)) :=
  h.2.scalarPower_rank n

/-- Scalar multiplication has the rank-based O-height d². -/
theorem scalar_height {π : 𝒪[K]} (h : X.HasHeightSquared π) :
    (X.formalModule.scalarHom π).HasHeight (Nat.card 𝓀[K])
      ((CentralSimple.reducedDegree K D) ^ 2) := h.2.scalar_height

/-- Extend both inverse order-linear maps along the coefficient map. -/
def Iso.mapSameUniverse {S : Type v} [CommRing S] [Algebra 𝒪[K] S]
    {X Y : SpecialModule K D ι R} (f : Iso X Y) (θ : R →ₐ[𝒪[K]] S) :
    Iso (X.mapSameUniverse θ) (Y.mapSameUniverse θ) :=
  ModuleLaw.OrderAction.Iso.map f θ

/-- The actual finite-height objects used by the coordinate part of Drinfeld's functor. -/
def HeightSquaredModule (π : 𝒪[K]) :=
  {X : SpecialModule K D ι R // X.HasHeightSquared π}

/-- Isomorphism of finite-height objects forgets only the proof of their height. -/
def heightSquaredIsoSetoid (π : 𝒪[K]) : Setoid (HeightSquaredModule (K := K)
    (D := D) (ι := ι) (R := R) π) where
  r X Y := Nonempty (Iso X.val Y.val)
  iseqv := ⟨fun X => ⟨Iso.refl X.val⟩,
    fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- Isomorphism classes of the actual special finite-height coordinate modules. -/
def HeightSquaredClass (π : 𝒪[K]) := Quotient (heightSquaredIsoSetoid
  (K := K) (D := D) (ι := ι) (R := R) π)

/-- Coefficient extension of an actual special module with its height certificate. -/
def HeightSquaredModule.mapSameUniverse {π : 𝒪[K]}
    (X : HeightSquaredModule (K := K) (D := D) (ι := ι) (R := R) π)
    {S : Type v} [CommRing S] [Algebra 𝒪[K] S] (θ : R →ₐ[𝒪[K]] S) :
    HeightSquaredModule (K := K) (D := D) (ι := ι) (R := S) π :=
  ⟨X.val.mapSameUniverse θ, X.property.map θ⟩

/-- Coefficient extension descends to actual order-linear isomorphism classes. -/
def HeightSquaredClass.mapSameUniverse {π : 𝒪[K]}
    {S : Type v} [CommRing S] [Algebra 𝒪[K] S] (θ : R →ₐ[𝒪[K]] S) :
    HeightSquaredClass (K := K) (D := D) (ι := ι) (R := R) π →
      HeightSquaredClass (K := K) (D := D) (ι := ι) (R := S) π :=
  Quotient.map (fun X => X.mapSameUniverse θ)
    (fun _ _ ⟨f⟩ => ⟨f.mapSameUniverse θ⟩)

end SpecialModule

end Langlands.FormalGroup.LocalDivision
