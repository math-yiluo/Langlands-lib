import Langlands.Weil.Local.ExtensionWeilRange
import Langlands.Weil.Local.Parameters
import Langlands.WeilDeligne.InductionAlong

/-!
# Restriction and induction of local representations and parameters along an extension

For an embedding `F → E` of p-adic fields, the actual Weil map `W_E → W_F` is an
open embedding with finite-index image that detects inertia and matches the norm
characters. Restriction goes from `W_F` to `W_E`, induction from `W_E` to `W_F`.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier →ₐ[Padic p] E.Carrier)

/-- Inertia is open in the actual local Weil group: it is the kernel of the
continuous degree map to the discrete integers. -/
private theorem localInertia_open (K : PadicField.{u} p) :
    IsOpen (localInertia K : Set (localWeilGroup K)) := by
  change IsOpen ((localDegree K) ⁻¹' ({1} : Set Degree))
  exact (isOpen_discrete _).preimage (localDegree K).continuous

/-- The Weil map sends `I_E` into `I_F`. -/
theorem extensionWeilMap_inertia (j : localInertia E) :
    extensionWeilMap F E f (j : localWeilGroup E) ∈ localInertia F :=
  (extensionWeilMap_mem_localInertia F E f j).mpr j.property

/-- The Weil map sends elements of nonzero degree to elements of nonzero degree. -/
theorem localDegreeInt_extensionWeilMap_ne_zero {w : localWeilGroup E}
    (hw : localDegreeInt E w ≠ 0) :
    localDegreeInt F (extensionWeilMap F E f w) ≠ 0 := by
  rw [localDegreeInt_extensionWeilMap]
  exact mul_ne_zero (by exact_mod_cast (extensionResidueDegree_pos F E f).ne') hw

/-! ## Restriction from `W_F` to `W_E` -/

/-- Restriction of a local Weil representation of `F` to `W_E`, on the same space. -/
def extensionRestrict (A : LocalWeilRepresentation.{u, w} F) :
    LocalWeilRepresentation.{v, w} E :=
  FiniteRepresentation.restrict (extensionWeilMap F E f).toMonoidHom A

/-- Restriction is Mathlib's restriction functor along the Weil map. -/
def extensionRestrictFunctor :
    LocalWeilRepresentation.{u, w} F ⥤ LocalWeilRepresentation.{v, w} E :=
  FiniteRepresentation.restrictFunctor (extensionWeilMap F E f).toMonoidHom

/-- Restriction keeps the carrier, hence the rank. -/
theorem rank_extensionRestrict (A : LocalWeilRepresentation.{u, w} F) :
    (extensionRestrict F E f A).rank = A.rank := rfl

/-- Restriction on genuine isomorphism classes. -/
def extensionRestrictClass : LocalWeilClasses.{u, w} F → LocalWeilClasses.{v, w} E :=
  FiniteRepresentation.restrictClass (extensionWeilMap F E f).toMonoidHom

/-- Restriction on rank-`n` isomorphism classes. -/
def extensionRestrictClassOfRank (n : ℕ) :
    LocalWeilClassesOfRank.{u, w} F n → LocalWeilClassesOfRank.{v, w} E n := by
  intro c
  refine ⟨extensionRestrictClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A => exact hc

/-- Restriction of a usual-topology continuous representation is continuous. -/
theorem isContinuous_extensionRestrict {A : LocalWeilRepresentation.{u, w} F}
    (hA : A.IsContinuous) : (extensionRestrict F E f A).IsContinuous := by
  let _ : TopologicalSpace (Module.End ℂ A) := moduleTopology ℂ (Module.End ℂ A)
  have hA' : Continuous A.representation := hA
  exact (hA'.comp (extensionWeilMap F E f).continuous :)

/-- Restriction of usual-topology continuous representations. -/
def extensionContinuousRestrict (A : LocalContinuousWeilObjects.{u, w} F) :
    LocalContinuousWeilObjects.{v, w} E :=
  ⟨extensionRestrict F E f A.val, isContinuous_extensionRestrict F E f A.property⟩

/-- Restriction of representations with open inertia kernel. -/
def extensionOpenInertiaRestrict (A : LocalOpenInertiaWeilObjects.{u, w} F) :
    LocalOpenInertiaWeilObjects.{v, w} E :=
  FiniteRepresentation.openInertiaRestrict (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap F E f).continuous
    (extensionWeilMap_inertia F E f) A

/-- Restriction on genuine classes with open inertia kernel. -/
def extensionOpenInertiaRestrictClass :
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{u, w} F => A.HasOpenInertiaKernel (localInertia F)) →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{v, w} E => A.HasOpenInertiaKernel (localInertia E)) :=
  FiniteRepresentation.openInertiaRestrictClass (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap F E f).continuous
    (extensionWeilMap_inertia F E f)

/-- The norm character of `F` pulled back along the Weil map is that of `E`. -/
theorem localNormCharacter_comp_extensionWeilMap (w : localWeilGroup E) :
    ((localNormCharacter F).toMonoidHom.comp (extensionWeilMap F E f).toMonoidHom) w =
      (localNormCharacter E).toMonoidHom w :=
  localNormCharacter_extensionWeilMap F E f w

/-- Restriction of a local pair: same carrier and monodromy, with the pulled-back
norm character of `F` restated as the norm character of `E`. -/
def extensionWDRestrict (A : LocalWeilDeligneRepresentation.{u, w} F) :
    LocalWeilDeligneRepresentation.{v, w} E :=
  WeilDeligneRepresentation.ofNormEq (localNormCharacter_comp_extensionWeilMap F E f)
    (WeilDeligneRepresentation.restrict (extensionWeilMap F E f).toMonoidHom A)

/-- The restricted pair keeps the monodromy operator. -/
@[simp]
theorem extensionWDRestrict_monodromy (A : LocalWeilDeligneRepresentation.{u, w} F) :
    (extensionWDRestrict F E f A).monodromy = A.monodromy := rfl

/-- Restriction of local pairs is a functor. -/
def extensionWDRestrictFunctor :
    LocalWeilDeligneRepresentation.{u, w} F ⥤ LocalWeilDeligneRepresentation.{v, w} E :=
  WeilDeligneRepresentation.restrictFunctor (extensionWeilMap F E f).toMonoidHom ⋙
    WeilDeligneRepresentation.ofNormEqFunctor (localNormCharacter_comp_extensionWeilMap F E f)

/-- Restriction of genuine pair equivalences. -/
def extensionWDRestrictEquiv {A B : LocalWeilDeligneRepresentation.{u, w} F}
    (e : WeilDeligneRepresentation.Equiv A B) :
    WeilDeligneRepresentation.Equiv (extensionWDRestrict F E f A) (extensionWDRestrict F E f B) :=
  WeilDeligneRepresentation.ofNormEqEquiv _
    (WeilDeligneRepresentation.restrictEquiv (extensionWeilMap F E f).toMonoidHom e)

/-- Restriction keeps the rank of a pair. -/
theorem rank_extensionWDRestrict (A : LocalWeilDeligneRepresentation.{u, w} F) :
    (extensionWDRestrict F E f A).rank = A.rank := rfl

/-- Restriction of local pairs on genuine isomorphism classes. -/
def extensionWDRestrictClass :
    WeilDeligneRepresentation.IsomorphismClasses.{0, u, w} ℂ (localWeilGroup F)
        (localNormCharacter F).toMonoidHom →
      WeilDeligneRepresentation.IsomorphismClasses.{0, v, w} ℂ (localWeilGroup E)
        (localNormCharacter E).toMonoidHom :=
  Quotient.map (extensionWDRestrict F E f) (fun _ _ ⟨e⟩ => ⟨extensionWDRestrictEquiv F E f e⟩)

/-- Restriction of local pairs on rank-`n` classes. -/
def extensionWDRestrictClassOfRank (n : ℕ) :
    LocalWeilDeligneClassesOfRank.{u, w} F n → LocalWeilDeligneClassesOfRank.{v, w} E n := by
  intro c
  refine ⟨extensionWDRestrictClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A => exact hc

/-- Restriction of a local parameter keeps the open inertia kernel. -/
def extensionParameterRestrict (A : LocalParameterObjects.{u, w} F) :
    LocalParameterObjects.{v, w} E :=
  ⟨extensionWDRestrict F E f A.val,
    (WeilDeligneRepresentation.parameterRestrict (localInertia F) (localInertia E)
      (extensionWeilMap F E f).toMonoidHom (extensionWeilMap F E f).continuous
      (extensionWeilMap_inertia F E f) A).property⟩

/-- Parameter restriction on genuine parameter classes. -/
def extensionParameterRestrictClass :
    LocalParameterClasses.{u, w} F → LocalParameterClasses.{v, w} E :=
  Quotient.map (extensionParameterRestrict F E f)
    (fun _ _ ⟨e⟩ => ⟨extensionWDRestrictEquiv F E f e⟩)

/-- Parameter restriction on rank-`n` parameter classes. -/
def extensionParameterRestrictClassOfRank (n : ℕ) :
    LocalParameterClassesOfRank.{u, w} F n → LocalParameterClassesOfRank.{v, w} E n := by
  intro c
  refine ⟨extensionParameterRestrictClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A => exact hc

/-- Restriction preserves Frobenius-semisimple parameters: an element of `W_E` of
nonzero degree maps to an element of `W_F` of nonzero degree. -/
theorem isLocalFrobeniusSemisimpleParameter_extensionWDRestrict
    {A : LocalWeilDeligneRepresentation.{u, w} F}
    (hA : IsLocalFrobeniusSemisimpleParameter F A) :
    IsLocalFrobeniusSemisimpleParameter E (extensionWDRestrict F E f A) :=
  ⟨(extensionParameterRestrict F E f ⟨A, hA.1⟩).property,
    fun w hw => hA.2 (extensionWeilMap F E f w)
      (localDegreeInt_extensionWeilMap_ne_zero F E f hw)⟩

/-- Restriction of Frobenius-semisimple parameter objects. -/
def extensionFrobeniusSemisimpleRestrict
    (A : {A : LocalWeilDeligneRepresentation.{u, w} F //
      IsLocalFrobeniusSemisimpleParameter F A}) :
    {A : LocalWeilDeligneRepresentation.{v, w} E //
      IsLocalFrobeniusSemisimpleParameter E A} :=
  ⟨extensionWDRestrict F E f A.val,
    isLocalFrobeniusSemisimpleParameter_extensionWDRestrict F E f A.property⟩

/-- Restriction on genuine Frobenius-semisimple parameter classes. -/
def extensionFrobeniusSemisimpleRestrictClass :
    WeilDeligneRepresentation.FrobeniusSemisimpleParameterClasses.{u, w}
        (ν := (localNormCharacter F).toMonoidHom) (localInertia F)
        (localDegree F).toMonoidHom →
      WeilDeligneRepresentation.FrobeniusSemisimpleParameterClasses.{v, w}
        (ν := (localNormCharacter E).toMonoidHom) (localInertia E)
        (localDegree E).toMonoidHom :=
  Quotient.map (extensionFrobeniusSemisimpleRestrict F E f)
    (fun _ _ ⟨e⟩ => ⟨extensionWDRestrictEquiv F E f e⟩)

/-- Restriction on rank-`n` Frobenius-semisimple parameter classes. -/
def extensionFrobeniusSemisimpleRestrictClassOfRank (n : ℕ) :
    LocalFrobeniusSemisimpleParameterClassesOfRank.{u, w} F n →
      LocalFrobeniusSemisimpleParameterClassesOfRank.{v, w} E n := by
  intro c
  refine ⟨extensionFrobeniusSemisimpleRestrictClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A => exact hc

/-! ## Induction from `W_E` to `W_F` -/

/-- Induction of a local Weil representation of `E` to `W_F` along the Weil map. -/
def extensionInduce (A : LocalWeilRepresentation.{v, w} E) :
    LocalWeilRepresentation.{u, max u w} F :=
  FiniteRepresentation.induceAlong (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f) A

/-- Induction of local Weil representations is a functor. -/
def extensionInduceFunctor :
    LocalWeilRepresentation.{v, w} E ⥤ LocalWeilRepresentation.{u, max u w} F :=
  FiniteRepresentation.induceAlongFunctor (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f)

/-- Induction of actual representation equivalences. -/
def extensionInduceEquiv {A B : LocalWeilRepresentation.{v, w} E}
    (e : FiniteRepresentation.Equiv A B) :
    FiniteRepresentation.Equiv (extensionInduce F E f A) (extensionInduce F E f B) :=
  FiniteRepresentation.induceAlongEquiv _ _ e

/-- Induction multiplies the rank by `[E : F]`. -/
theorem rank_extensionInduce (A : LocalWeilRepresentation.{v, w} E) :
    (extensionInduce F E f A).rank = extensionDegree F E f * A.rank := by
  rw [extensionInduce, FiniteRepresentation.rank_induceAlong, extensionWeilMap_range_index]

/-- Induction on genuine isomorphism classes. -/
def extensionInduceClass : LocalWeilClasses.{v, w} E → LocalWeilClasses.{u, max u w} F :=
  FiniteRepresentation.induceAlongClass (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f)

/-- Induction from rank-`n` classes to rank-`[E : F] * n` classes. -/
def extensionInduceClassOfRank (n : ℕ) :
    LocalWeilClassesOfRank.{v, w} E n →
      LocalWeilClassesOfRank.{u, max u w} F (extensionDegree F E f * n) := by
  intro c
  refine ⟨extensionInduceClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A =>
    change (extensionInduce F E f A).rank = extensionDegree F E f * n
    rw [rank_extensionInduce]
    change A.rank = n at hc
    rw [hc]

/-- Induction of representations with open inertia kernel. -/
def extensionOpenInertiaInduce (A : LocalOpenInertiaWeilObjects.{v, w} E) :
    LocalOpenInertiaWeilObjects.{u, max u w} F :=
  FiniteRepresentation.openInertiaInduceAlong (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap_isOpenEmbedding F E f)
    (localInertia_open F) (fun w => (extensionWeilMap_mem_localInertia F E f w).mp) A

/-- Induction on genuine classes with open inertia kernel. -/
def extensionOpenInertiaInduceClass :
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{v, w} E => A.HasOpenInertiaKernel (localInertia E)) →
    FiniteRepresentation.IsomorphismClassesWith
      (fun A : LocalWeilRepresentation.{u, max u w} F =>
        A.HasOpenInertiaKernel (localInertia F)) :=
  FiniteRepresentation.openInertiaInduceAlongClass (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap_isOpenEmbedding F E f)
    (localInertia_open F) (fun w => (extensionWeilMap_mem_localInertia F E f w).mp)

/-- Induction of a local pair of `E` to `W_F`, with monodromy
`N(φ)(g) = ‖g‖ N(φ(g))`. -/
def extensionWDInduce (A : LocalWeilDeligneRepresentation.{v, w} E) :
    LocalWeilDeligneRepresentation.{u, max u w} F :=
  WeilDeligneRepresentation.induceAlong (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f) (localNormCharacter_extensionWeilMap F E f) A

/-- Induction of local pairs is a functor. -/
def extensionWDInduceFunctor :
    LocalWeilDeligneRepresentation.{v, w} E ⥤ LocalWeilDeligneRepresentation.{u, max u w} F :=
  WeilDeligneRepresentation.induceAlongFunctor (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f) (localNormCharacter_extensionWeilMap F E f)

/-- Induction of genuine pair equivalences. -/
def extensionWDInduceEquiv {A B : LocalWeilDeligneRepresentation.{v, w} E}
    (e : WeilDeligneRepresentation.Equiv A B) :
    WeilDeligneRepresentation.Equiv (extensionWDInduce F E f A) (extensionWDInduce F E f B) :=
  WeilDeligneRepresentation.induceAlongEquiv _ _ _ e

/-- Induction multiplies the rank of a pair by `[E : F]`. -/
theorem rank_extensionWDInduce (A : LocalWeilDeligneRepresentation.{v, w} E) :
    (extensionWDInduce F E f A).rank = extensionDegree F E f * A.rank := by
  rw [extensionWDInduce, WeilDeligneRepresentation.rank_induceAlong,
    extensionWeilMap_range_index]

/-- Induction of local pairs on genuine isomorphism classes. -/
def extensionWDInduceClass :
    WeilDeligneRepresentation.IsomorphismClasses.{0, v, w} ℂ (localWeilGroup E)
        (localNormCharacter E).toMonoidHom →
      WeilDeligneRepresentation.IsomorphismClasses.{0, u, max u w} ℂ (localWeilGroup F)
        (localNormCharacter F).toMonoidHom :=
  WeilDeligneRepresentation.induceAlongClass (extensionWeilMap F E f).toMonoidHom
    (extensionWeilMap_injective F E f) (localNormCharacter_extensionWeilMap F E f)

/-- Induction of local pairs from rank `n` to rank `[E : F] * n`. -/
def extensionWDInduceClassOfRank (n : ℕ) :
    LocalWeilDeligneClassesOfRank.{v, w} E n →
      LocalWeilDeligneClassesOfRank.{u, max u w} F (extensionDegree F E f * n) := by
  intro c
  refine ⟨extensionWDInduceClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A =>
    change (extensionWDInduce F E f A).rank = extensionDegree F E f * n
    rw [rank_extensionWDInduce]
    change A.rank = n at hc
    rw [hc]

/-- Induction of a local parameter keeps the open inertia kernel. -/
def extensionParameterInduce (A : LocalParameterObjects.{v, w} E) :
    LocalParameterObjects.{u, max u w} F :=
  WeilDeligneRepresentation.parameterInduceAlong (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap_isOpenEmbedding F E f)
    (localInertia_open F) (fun w => (extensionWeilMap_mem_localInertia F E f w).mp)
    (localNormCharacter_extensionWeilMap F E f) A

/-- Parameter induction on genuine parameter classes. -/
def extensionParameterInduceClass :
    LocalParameterClasses.{v, w} E → LocalParameterClasses.{u, max u w} F :=
  WeilDeligneRepresentation.parameterInduceAlongClass (localInertia F) (localInertia E)
    (extensionWeilMap F E f).toMonoidHom (extensionWeilMap_isOpenEmbedding F E f)
    (localInertia_open F) (fun w => (extensionWeilMap_mem_localInertia F E f w).mp)
    (localNormCharacter_extensionWeilMap F E f)

/-- Parameter induction from rank `n` to rank `[E : F] * n`. -/
def extensionParameterInduceClassOfRank (n : ℕ) :
    LocalParameterClassesOfRank.{v, w} E n →
      LocalParameterClassesOfRank.{u, max u w} F (extensionDegree F E f * n) := by
  intro c
  refine ⟨extensionParameterInduceClass F E f c.val, ?_⟩
  obtain ⟨c, hc⟩ := c
  induction c using Quotient.inductionOn with
  | h A =>
    change (extensionWDInduce F E f A.val).rank = extensionDegree F E f * n
    rw [rank_extensionWDInduce]
    change A.val.rank = n at hc
    rw [hc]

end Langlands.Weil.Local
