import Langlands.ClassField.Global.ArchimedeanLocalWeilMap
import Langlands.Automorphic.ArchimedeanPlaceParameterClasses
import Langlands.Automorphic.Unramified.AbsoluteWeilAssociation

/-! # Archimedean components of Weil representations and archimedean matching

The archimedean components of representations of the relative and absolute global Weil
groups along the archimedean local Weil maps, their presentations by the Library's
archimedean blocks, and the matching of a representation of `W_F` with an actual cuspidal
class at an infinite place: the archimedean component of the Weil representation and the
archimedean component of the cuspidal class have the same presentation. No local map,
representation, presentation or parameter is constructed or asserted to exist.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField
open Langlands.Weil.Archimedean Langlands.LocalFactor.Archimedean Langlands.Automorphic

universe u uV uW

namespace RelativeWeilGroup

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] {c : FundamentalClass.ClassFamily.{u}}

/-- The archimedean component `A ∘ ι` of a representation of `W_{E/F}` along a map
`ι : W_ℝ → W_{E/F}`, on the original carrier. -/
def realComponent (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : RealWeil →ₜ* RelativeWeilGroup c F E) : FiniteRepresentation.{0, 0, uV} ℂ RealWeil :=
  FiniteRepresentation.restrict ι.toMonoidHom A

/-- The archimedean component `A ∘ ι` along a map `ι : W_ℂ → W_{E/F}`. -/
def complexComponent (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : ComplexWeil →ₜ* RelativeWeilGroup c F E) :
    FiniteRepresentation.{0, 0, uV} ℂ ComplexWeil :=
  FiniteRepresentation.restrict ι.toMonoidHom A

/-- The real archimedean component of `A` along `ι` is presented by the real blocks `ds`: it
is equivalent to their published sum model. -/
def HasRealPresentation (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : RealWeil →ₜ* RelativeWeilGroup c F E) (ds : List RealBlock) : Prop :=
  Nonempty (FiniteRepresentation.Equiv (realComponent A ι) (realModel ds).val)

/-- The complex archimedean component of `A` along `ι` is presented by the complex blocks
`ds`. -/
def HasComplexPresentation (A : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (ι : ComplexWeil →ₜ* RelativeWeilGroup c F E) (ds : List ComplexCharacterData) : Prop :=
  Nonempty (FiniteRepresentation.Equiv (complexComponent A ι) (complexModel ds).val)

end RelativeWeilGroup

namespace WeilMapSystem

variable {c : FundamentalClass.ClassFamily.{u}} {F : Type u} [Field F] [NumberField F]
  {Ω : Type u} [Field Ω] [Algebra F Ω] {h : FundamentalClass.Restriction c}
  (S : WeilMapSystem c F Ω h)

/-- The archimedean component `A ∘ θ` of a representation of `W_F` along a map
`θ : W_ℝ → W_F`. -/
def realComponent (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (θ : RealWeil →ₜ* S.WeilGroup) : FiniteRepresentation.{0, 0, uV} ℂ RealWeil :=
  FiniteRepresentation.restrict θ.toMonoidHom A

/-- The archimedean component `A ∘ θ` along a map `θ : W_ℂ → W_F`. -/
def complexComponent (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (θ : ComplexWeil →ₜ* S.WeilGroup) : FiniteRepresentation.{0, 0, uV} ℂ ComplexWeil :=
  FiniteRepresentation.restrict θ.toMonoidHom A

/-- `A` has archimedean parameter `ds` at the real embedding `φ`: a real local-to-global Weil
map at `φ` exists, and the real archimedean component along every such map is equivalent to
the sum model of the real blocks `ds`. -/
def HasRealArchimedeanParameter (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (φ : F →+* ℂ) (ds : List RealBlock) : Prop :=
  (∃ θ : RealWeil →ₜ* S.WeilGroup, S.IsRealLocalWeilMap φ θ) ∧
    ∀ θ : RealWeil →ₜ* S.WeilGroup, S.IsRealLocalWeilMap φ θ →
      Nonempty (FiniteRepresentation.Equiv (S.realComponent A θ) (realModel ds).val)

/-- `A` has archimedean parameter `ds` at the complex embedding `φ`: a complex local-to-global
Weil map at `φ` exists, and the complex archimedean component along every such map is
equivalent to the sum model of the complex blocks `ds`. -/
def HasComplexArchimedeanParameter (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (φ : F →+* ℂ) (ds : List ComplexCharacterData) : Prop :=
  (∃ θ : ComplexWeil →ₜ* S.WeilGroup, S.IsComplexLocalWeilMap φ θ) ∧
    ∀ θ : ComplexWeil →ₜ* S.WeilGroup, S.IsComplexLocalWeilMap φ θ →
      Nonempty (FiniteRepresentation.Equiv (S.complexComponent A θ) (complexModel ds).val)

section Invariance

variable {S} {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
  {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup}

/-- An equivalence of representations of `W_F` restricts to their real archimedean
components. -/
def realComponentEquiv (φ : FiniteRepresentation.Equiv A B) (θ : RealWeil →ₜ* S.WeilGroup) :
    FiniteRepresentation.Equiv (S.realComponent A θ) (S.realComponent B θ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (θ g)

/-- An equivalence of representations of `W_F` restricts to their complex archimedean
components. -/
def complexComponentEquiv (φ : FiniteRepresentation.Equiv A B)
    (θ : ComplexWeil →ₜ* S.WeilGroup) :
    FiniteRepresentation.Equiv (S.complexComponent A θ) (S.complexComponent B θ) :=
  Representation.Equiv.mk φ.toLinearEquiv fun g => φ.toIntertwiningMap.isIntertwining' (θ g)

/-- The real archimedean parameter depends only on the equivalence class of `A`. -/
theorem HasRealArchimedeanParameter.of_equiv {φ' : F →+* ℂ} {ds : List RealBlock}
    (φ : FiniteRepresentation.Equiv A B) (hA : S.HasRealArchimedeanParameter A φ' ds) :
    S.HasRealArchimedeanParameter B φ' ds := by
  refine ⟨hA.1, fun θ hθ => ?_⟩
  obtain ⟨e⟩ := hA.2 θ hθ
  exact ⟨(realComponentEquiv φ θ).symm.trans e⟩

/-- The complex archimedean parameter depends only on the equivalence class of `A`. -/
theorem HasComplexArchimedeanParameter.of_equiv {φ' : F →+* ℂ}
    {ds : List ComplexCharacterData} (φ : FiniteRepresentation.Equiv A B)
    (hA : S.HasComplexArchimedeanParameter A φ' ds) :
    S.HasComplexArchimedeanParameter B φ' ds := by
  refine ⟨hA.1, fun θ hθ => ?_⟩
  obtain ⟨e⟩ := hA.2 θ hθ
  exact ⟨(complexComponentEquiv φ θ).symm.trans e⟩

end Invariance

section Matching

variable [CompactSpace (Langlands.Global.AdeleQuotient F)]

/-- `A` matches the actual cuspidal class `π` at the real place `v`: some list of real blocks is
the archimedean parameter of `A` at the real embedding of `v` and the place parameter of `π`
at `v`. -/
def IsRealArchimedeanMatch (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (π : PositiveRankCuspidalClass F)
    (v : {v : InfinitePlace F // v.IsReal}) : Prop :=
  ∃ ds : List RealBlock,
    S.HasRealArchimedeanParameter A v.1.embedding ds ∧ π.HasRealPlaceParameter v ds

/-- `A` matches the actual cuspidal class `π` at the complex place `v`, with `F_v` identified
with `ℂ` through Mathlib's chosen embedding `v.embedding`, the convention of the published
place actions: some list of complex blocks is the archimedean parameter of `A` at
`v.embedding` and the place parameter of `π` at `v`. -/
def IsComplexArchimedeanMatch (A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup)
    (π : PositiveRankCuspidalClass F)
    (v : {v : InfinitePlace F // v.IsComplex}) : Prop :=
  ∃ ds : List ComplexCharacterData,
    S.HasComplexArchimedeanParameter A v.1.embedding ds ∧ π.HasComplexPlaceParameter v ds

/-- A real archimedean match forces the rank of `A`'s archimedean component to be the rank of
`π`. -/
theorem IsRealArchimedeanMatch.exists_realRank_eq
    {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {π : PositiveRankCuspidalClass F} {v : {v : InfinitePlace F // v.IsReal}}
    (h : S.IsRealArchimedeanMatch A π v) :
    ∃ ds : List RealBlock, S.HasRealArchimedeanParameter A v.1.embedding ds ∧
      realRank ds = π.rank := by
  obtain ⟨ds, hA, hπ⟩ := h
  exact ⟨ds, hA, hπ.realRank_eq⟩

/-- Archimedean matching depends only on the equivalence class of `A`. -/
theorem IsRealArchimedeanMatch.of_equiv {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup} {π : PositiveRankCuspidalClass F}
    {v : {v : InfinitePlace F // v.IsReal}} (φ : FiniteRepresentation.Equiv A B)
    (h : S.IsRealArchimedeanMatch A π v) : S.IsRealArchimedeanMatch B π v := by
  obtain ⟨ds, hA, hπ⟩ := h
  exact ⟨ds, hA.of_equiv φ, hπ⟩

/-- Archimedean matching depends only on the equivalence class of `A`. -/
theorem IsComplexArchimedeanMatch.of_equiv {A : FiniteRepresentation.{0, u, uV} ℂ S.WeilGroup}
    {B : FiniteRepresentation.{0, u, uW} ℂ S.WeilGroup} {π : PositiveRankCuspidalClass F}
    {v : {v : InfinitePlace F // v.IsComplex}} (φ : FiniteRepresentation.Equiv A B)
    (h : S.IsComplexArchimedeanMatch A π v) : S.IsComplexArchimedeanMatch B π v := by
  obtain ⟨ds, hA, hπ⟩ := h
  exact ⟨ds, hA.of_equiv φ, hπ⟩

end Matching

end WeilMapSystem

end Langlands.ClassField.Global
