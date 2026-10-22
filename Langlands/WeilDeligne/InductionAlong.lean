import Langlands.WeilDeligne.ParameterInduction
import Langlands.WeilDeligne.ParameterRestriction

/-!
# Induction along an injective homomorphism with finite-index range

Finite-index induction is constructed for an actual subgroup. An injective
homomorphism `ι : H →* G` identifies `H` with its range. A representation or
pair of `H` is moved to the range by restriction along the inverse of the
corestriction, and is then induced. For pairs, the norm characters must agree
along `ι`.
-/

noncomputable section

universe uK uG uH uV uW

open CategoryTheory

namespace Langlands

namespace InductionAlong

variable {G : Type uG} {H : Type uH} [Group G] [Group H]

/-- The inverse of the corestriction of an injective homomorphism to its range. -/
def rangeInverse (ι : H →* G) (hι : Function.Injective ι) : ι.range →* H :=
  (MonoidHom.ofInjective hι).symm.toMonoidHom

@[simp]
theorem apply_rangeInverse (ι : H →* G) (hι : Function.Injective ι) (s : ι.range) :
    ι (rangeInverse ι hι s) = s :=
  MonoidHom.apply_ofInjective_symm hι s

@[simp]
theorem rangeInverse_apply (ι : H →* G) (hι : Function.Injective ι) (h : H) :
    rangeInverse ι hι ⟨ι h, h, rfl⟩ = h :=
  hι (apply_rangeInverse ι hι ⟨ι h, h, rfl⟩)

variable [TopologicalSpace G] [TopologicalSpace H]

/-- For a topological embedding, the inverse on the range is continuous. -/
theorem continuous_rangeInverse (ι : H →* G) (hι : Topology.IsEmbedding ι) :
    Continuous (rangeInverse ι hι.injective) := by
  rw [hι.continuous_iff]
  have h : (ι ∘ rangeInverse ι hι.injective) = fun s : ι.range => (s : G) := by
    funext s
    exact apply_rangeInverse ι hι.injective s
  rw [h]
  exact continuous_subtype_val

/-- The range of an open embedding is an open subgroup. -/
theorem isOpen_range (ι : H →* G) (hι : Topology.IsOpenEmbedding ι) :
    IsOpen (ι.range : Set G) := by
  rw [MonoidHom.coe_range]
  exact hι.isOpen_range

end InductionAlong

open InductionAlong

namespace FiniteRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH} [Field K] [Group G] [Group H]

/-- Induction along an injective homomorphism with finite-index range. -/
def induceAlong (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (A : FiniteRepresentation.{uK, uH, uV} K H) :
    FiniteRepresentation.{uK, uG, max uG uV} K G :=
  induce ι.range (restrict (rangeInverse ι hι) A)

/-- Induction along `ι` is a functor. -/
def induceAlongFunctor (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex] :
    FiniteRepresentation.{uK, uH, uV} K H ⥤ FiniteRepresentation.{uK, uG, max uG uV} K G :=
  restrictFunctor (rangeInverse ι hι) ⋙ induceFunctor ι.range

/-- Induction along `ι` of actual representation equivalences. -/
def induceAlongEquiv (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    {A B : FiniteRepresentation.{uK, uH, uV} K H} (e : Equiv A B) :
    Equiv (induceAlong ι hι A) (induceAlong ι hι B) :=
  induceEquiv ι.range (restrictEquiv (rangeInverse ι hι) e)

/-- Induction along `ι` on genuine isomorphism classes. -/
def induceAlongClass (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex] :
    IsomorphismClasses.{uK, uH, uV} K H → IsomorphismClasses.{uK, uG, max uG uV} K G :=
  Quotient.map (induceAlong ι hι) (fun _ _ ⟨e⟩ => ⟨induceAlongEquiv ι hι e⟩)

/-- The rank is multiplied by the index of the range, allowing rank zero. -/
theorem rank_induceAlong (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (A : FiniteRepresentation.{uK, uH, uV} K H) :
    (induceAlong ι hι A).rank = ι.range.index * A.rank :=
  rank_induce ι.range (restrict (rangeInverse ι hι) A)

section OpenInertia

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]

/-- Induction along an open embedding with finite-index range preserves an open
inertia kernel when the ambient inertia is open and its preimage lies in the
source inertia. -/
theorem hasOpenInertiaKernel_induceAlong (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J)
    {A : FiniteRepresentation.{0, uH, uV} ℂ H} (hA : A.HasOpenInertiaKernel J) :
    (induceAlong ι hι.injective A).HasOpenInertiaKernel I :=
  hasOpenInertiaKernel_induce ι.range I (isOpen_range ι hι) hI _
    (hasOpenInertiaKernel_restrict J (I.subgroupOf ι.range) (rangeInverse ι hι.injective)
      (continuous_rangeInverse ι hι.isEmbedding)
      (fun j => hJ _ (by
        rw [apply_rangeInverse]
        exact Subgroup.mem_subgroupOf.mp j.property)) hA)

/-- Induction along `ι` on actual open-inertia objects. -/
def openInertiaInduceAlong (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J) (A : OpenInertiaObjects.{uH, uV} J) :
    OpenInertiaObjects.{uG, max uG uV} I :=
  ⟨induceAlong ι hι.injective A.val, hasOpenInertiaKernel_induceAlong I J ι hι hI hJ A.property⟩

/-- Induction along `ι` on genuine open-inertia representation classes. -/
def openInertiaInduceAlongClass (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J) :
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uH, uV} ℂ H =>
      A.HasOpenInertiaKernel J) →
    IsomorphismClassesWith (fun A : FiniteRepresentation.{0, uG, max uG uV} ℂ G =>
      A.HasOpenInertiaKernel I) :=
  Quotient.map (openInertiaInduceAlong I J ι hι hI hJ)
    (fun _ _ ⟨e⟩ => ⟨induceAlongEquiv ι hι.injective e⟩)

end OpenInertia

end FiniteRepresentation

namespace WeilDeligneRepresentation

variable {K : Type uK} {G : Type uG} {H : Type uH} [Field K] [Group G] [Group H]

section NormChange

variable {ν ν' : G →* Kˣ}

/-- The same pair, regarded with a pointwise equal norm character. Carrier,
action and monodromy are unchanged; only covariance is restated. -/
def ofNormEq (hν : ∀ g, ν g = ν' g) (A : WeilDeligneRepresentation.{uK, uG, uV} K G ν) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν' where
  toFiniteRepresentation := A.toFiniteRepresentation
  monodromy := A.monodromy
  nilpotent := A.nilpotent
  covariance g := by
    rw [← hν g]
    exact A.covariance g

/-- A pair morphism is unchanged by the norm change. -/
def ofNormEqMap (hν : ∀ g, ν g = ν' g) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (f : Hom A B) :
    Hom (ofNormEq hν A) (ofNormEq hν B) :=
  ⟨f.intertwiner, f.comm_monodromy⟩

/-- The norm change is a functor between the two pair categories. -/
def ofNormEqFunctor (hν : ∀ g, ν g = ν' g) :
    WeilDeligneRepresentation.{uK, uG, uV} K G ν ⥤
      WeilDeligneRepresentation.{uK, uG, uV} K G ν' where
  obj := ofNormEq hν
  map := ofNormEqMap hν
  map_id _ := by apply Hom.ext; rfl
  map_comp _ _ := by apply Hom.ext; rfl

/-- A pair equivalence is unchanged by the norm change. -/
def ofNormEqEquiv (hν : ∀ g, ν g = ν' g) {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν} (e : Equiv A B) :
    Equiv (ofNormEq hν A) (ofNormEq hν B) :=
  ⟨e.representationEquiv, e.comm_monodromy⟩

end NormChange

variable {ν : G →* Kˣ} {νH : H →* Kˣ}

/-- Compatible norms along `ι` give the restricted ambient norm on its range. -/
theorem norm_rangeInverse (ι : H →* G) (hι : Function.Injective ι)
    (hν : ∀ h, ν (ι h) = νH h) (s : ι.range) :
    (νH.comp (rangeInverse ι hι)) s = (ν.comp ι.range.subtype) s := by
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← hν, apply_rangeInverse]
  rfl

/-- Induction of a pair along an injective homomorphism with finite-index range
and compatible norm characters. -/
def induceAlong (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (hν : ∀ h, ν (ι h) = νH h) (A : WeilDeligneRepresentation.{uK, uH, uV} K H νH) :
    WeilDeligneRepresentation.{uK, uG, max uG uV} K G ν :=
  induce ι.range (ofNormEq (norm_rangeInverse ι hι hν) (restrict (rangeInverse ι hι) A))

/-- The induced monodromy is the weighted pointwise operator. -/
@[simp]
theorem induceAlong_monodromy_apply (ι : H →* G) (hι : Function.Injective ι)
    [ι.range.FiniteIndex] (hν : ∀ h, ν (ι h) = νH h)
    (A : WeilDeligneRepresentation.{uK, uH, uV} K H νH)
    (f : induceAlong ι hι hν A) (g : G) :
    ((induceAlong ι hι hν A).monodromy f).val g = (ν g : K) • A.monodromy (f.val g) := rfl

/-- Induction of pairs along `ι` is a functor. -/
def induceAlongFunctor (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (hν : ∀ h, ν (ι h) = νH h) :
    WeilDeligneRepresentation.{uK, uH, uV} K H νH ⥤
      WeilDeligneRepresentation.{uK, uG, max uG uV} K G ν :=
  restrictFunctor (rangeInverse ι hι) ⋙ ofNormEqFunctor (norm_rangeInverse ι hι hν) ⋙
    induceFunctor ι.range

/-- Induction along `ι` of genuine pair equivalences. -/
def induceAlongEquiv (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (hν : ∀ h, ν (ι h) = νH h) {A B : WeilDeligneRepresentation.{uK, uH, uV} K H νH}
    (e : Equiv A B) : Equiv (induceAlong ι hι hν A) (induceAlong ι hι hν B) :=
  induceEquiv ι.range (ofNormEqEquiv _ (restrictEquiv (rangeInverse ι hι) e))

/-- Induction along `ι` on genuine pair isomorphism classes. -/
def induceAlongClass (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (hν : ∀ h, ν (ι h) = νH h) :
    IsomorphismClasses.{uK, uH, uV} K H νH → IsomorphismClasses.{uK, uG, max uG uV} K G ν :=
  Quotient.map (induceAlong ι hι hν) (fun _ _ ⟨e⟩ => ⟨induceAlongEquiv ι hι hν e⟩)

/-- The rank of a pair induced along `ι`, allowing rank zero. -/
theorem rank_induceAlong (ι : H →* G) (hι : Function.Injective ι) [ι.range.FiniteIndex]
    (hν : ∀ h, ν (ι h) = νH h) (A : WeilDeligneRepresentation.{uK, uH, uV} K H νH) :
    (induceAlong ι hι hν A).rank = ι.range.index * A.rank :=
  rank_induce ι.range _

section Complex

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace H]
  {ν : G →* ℂˣ} {νH : H →* ℂˣ}

/-- Induce an actual open-inertia parameter along an open embedding with
finite-index range. The ambient inertia is explicitly open, its preimage lies in
the source inertia, and the norm characters agree along the embedding. -/
def parameterInduceAlong (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J) (hν : ∀ h, ν (ι h) = νH h)
    (A : ParameterObjects.{uH, uV} (ν := νH) J) :
    ParameterObjects.{uG, max uG uV} (ν := ν) I :=
  ⟨induceAlong ι hι.injective hν A.val,
    FiniteRepresentation.hasOpenInertiaKernel_induceAlong I J ι hι hI hJ A.property⟩

/-- Induction along `ι` on genuine parameter classes. -/
def parameterInduceAlongClass (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J) (hν : ∀ h, ν (ι h) = νH h) :
    ParameterClasses.{uH, uV} (ν := νH) J → ParameterClasses.{uG, max uG uV} (ν := ν) I :=
  Quotient.map (parameterInduceAlong I J ι hι hI hJ hν)
    (fun _ _ ⟨e⟩ => ⟨induceAlongEquiv ι hι.injective hν e⟩)

/-- Induction along `ι` on rank-indexed parameter classes, from rank `n` to
rank `[G : ι(H)] * n`. -/
def parameterInduceAlongClassOfRank (I : Subgroup G) (J : Subgroup H) (ι : H →* G)
    (hι : Topology.IsOpenEmbedding ι) [ι.range.FiniteIndex] (hI : IsOpen (I : Set G))
    (hJ : ∀ h : H, ι h ∈ I → h ∈ J) (hν : ∀ h, ν (ι h) = νH h) (n : ℕ) :
    ParameterClassesOfRank.{uH, uV} (ν := νH) J n →
      ParameterClassesOfRank.{uG, max uG uV} (ν := ν) I (ι.range.index * n) := by
  intro c
  refine ⟨parameterInduceAlongClass I J ι hι hI hJ hν c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A =>
    change (induceAlong ι hι.injective hν A.val).rank = ι.range.index * n
    rw [rank_induceAlong]
    change A.val.rank = n at hc
    rw [hc]

end Complex

end WeilDeligneRepresentation

end Langlands
