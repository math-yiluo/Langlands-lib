import Langlands.LinearAlgebra.JordanChevalleyFunctoriality
import Mathlib.RingTheory.Finiteness.Basic

/-! # Compatible Jordan components of locally finite endomorphisms -/

noncomputable section

universe u v w

open Module

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    {W : Type w} [AddCommGroup W] [Module k W]

/-- A finite-dimensional invariant subspace of an endomorphism. -/
structure FiniteInvariantSubspace (f : End k V) where
  carrier : Submodule k V
  finite : Module.Finite k carrier
  invariant : carrier ∈ f.invtSubmodule

attribute [instance] FiniteInvariantSubspace.finite

/-- Every vector belongs to a finite-dimensional invariant subspace. -/
def IsLocallyFinite (f : End k V) : Prop :=
  ∀ x : V, ∃ P : FiniteInvariantSubspace f, x ∈ P.carrier

namespace FiniteInvariantSubspace

variable {f : End k V}

/-- The restriction to a finite-dimensional invariant subspace. -/
def restrict (P : FiniteInvariantSubspace f) : End k P.carrier :=
  f.restrict P.invariant

/-- The sum of two finite-dimensional invariant subspaces. -/
def sup (P Q : FiniteInvariantSubspace f) : FiniteInvariantSubspace f where
  carrier := P.carrier ⊔ Q.carrier
  finite := inferInstance
  invariant := Module.End.invtSubmodule.sup_mem P.invariant Q.invariant

variable [PerfectField k]

/-- The finite semisimple component, viewed in the ambient space. -/
def semisimpleMap (P : FiniteInvariantSubspace f) : P.carrier →ₗ[k] V :=
  P.carrier.subtype ∘ₗ jordanSemisimplePart P.restrict

/-- Inclusion of finite invariant subspaces preserves their semisimple maps. -/
theorem semisimpleMap_inclusion (P Q : FiniteInvariantSubspace f)
    (hPQ : P.carrier ≤ Q.carrier) (x : P.carrier) :
    Q.semisimpleMap (Submodule.inclusion hPQ x) = P.semisimpleMap x := by
  have h := jordanSemisimplePart_intertwines
    (f := P.restrict) (g := Q.restrict) (Submodule.inclusion hPQ) (by rfl)
  exact congrArg Subtype.val (LinearMap.congr_fun h x)

end FiniteInvariantSubspace

variable [PerfectField k]

/-- Choose the finite semisimple value using a finite invariant subspace. -/
def locallyFiniteJordanValue (f : End k V) (hf : IsLocallyFinite f) (x : V) : V :=
  (hf x).choose.semisimpleMap ⟨x, (hf x).choose_spec⟩

/-- The value is independent of the chosen finite invariant subspace. -/
theorem locallyFiniteJordanValue_eq (f : End k V) (hf : IsLocallyFinite f)
    (P : FiniteInvariantSubspace f) (x : P.carrier) :
    locallyFiniteJordanValue f hf x = P.semisimpleMap x := by
  let Q := (hf x).choose
  let y : Q.carrier := ⟨x, (hf x).choose_spec⟩
  change Q.semisimpleMap y = P.semisimpleMap x
  calc
    Q.semisimpleMap y = (P.sup Q).semisimpleMap
        (Submodule.inclusion le_sup_right y) :=
      (Q.semisimpleMap_inclusion (P.sup Q) le_sup_right y).symm
    _ = P.semisimpleMap x :=
      P.semisimpleMap_inclusion (P.sup Q) le_sup_left x

/-- The compatible semisimple components form a linear endomorphism. -/
def locallyFiniteSemisimplePart (f : End k V) (hf : IsLocallyFinite f) : End k V where
  toFun := locallyFiniteJordanValue f hf
  map_add' x y := by
    obtain ⟨P, hx⟩ := hf x
    obtain ⟨Q, hy⟩ := hf y
    let S := P.sup Q
    let xS : S.carrier := ⟨x, Submodule.mem_sup_left hx⟩
    let yS : S.carrier := ⟨y, Submodule.mem_sup_right hy⟩
    have hxS := locallyFiniteJordanValue_eq f hf S xS
    have hyS := locallyFiniteJordanValue_eq f hf S yS
    have hxyS := locallyFiniteJordanValue_eq f hf S (xS + yS)
    exact hxyS.trans ((map_add S.semisimpleMap xS yS).trans (congrArg₂ (· + ·) hxS hyS).symm)
  map_smul' a x := by
    obtain ⟨P, hx⟩ := hf x
    let xP : P.carrier := ⟨x, hx⟩
    have hxP := locallyFiniteJordanValue_eq f hf P xP
    have haxP := locallyFiniteJordanValue_eq f hf P (a • xP)
    exact haxP.trans ((map_smul P.semisimpleMap a xP).trans (congrArg (a • ·) hxP).symm)

/-- On every finite invariant subspace the global part equals the finite part. -/
theorem locallyFiniteSemisimplePart_eq (f : End k V) (hf : IsLocallyFinite f)
    (P : FiniteInvariantSubspace f) (x : P.carrier) :
    locallyFiniteSemisimplePart f hf x = P.semisimpleMap x :=
  locallyFiniteJordanValue_eq f hf P x

/-- An intertwiner from a finite-dimensional space preserves the global part. -/
theorem locallyFiniteSemisimplePart_intertwines_finite [FiniteDimensional k W]
    {f : End k V} (hf : IsLocallyFinite f) {a : End k W}
    (T : W →ₗ[k] V) (h : f.comp T = T.comp a) :
    (locallyFiniteSemisimplePart f hf).comp T = T.comp (jordanSemisimplePart a) := by
  let Q : FiniteInvariantSubspace f :=
    { carrier := LinearMap.range T
      finite := Module.Finite.range T
      invariant := by
        intro y hy
        obtain ⟨x, rfl⟩ := hy
        exact ⟨a x, (LinearMap.congr_fun h x).symm⟩ }
  have hQ : Q.restrict.comp T.rangeRestrict = T.rangeRestrict.comp a := by
    ext x
    exact LinearMap.congr_fun h x
  have hpart := jordanSemisimplePart_intertwines T.rangeRestrict hQ
  ext x
  calc
    locallyFiniteSemisimplePart f hf (T x) =
        Q.semisimpleMap (T.rangeRestrict x) :=
      locallyFiniteSemisimplePart_eq f hf Q (T.rangeRestrict x)
    _ = T (jordanSemisimplePart a x) :=
      congrArg Subtype.val (LinearMap.congr_fun hpart x)

/-- Every linear intertwiner between locally finite endomorphisms preserves
their compatible global semisimple parts. -/
theorem locallyFiniteSemisimplePart_intertwines
    {f : End k V} {g : End k W} (hf : IsLocallyFinite f) (hg : IsLocallyFinite g)
    (T : V →ₗ[k] W) (h : g.comp T = T.comp f) :
    (locallyFiniteSemisimplePart g hg).comp T =
      T.comp (locallyFiniteSemisimplePart f hf) := by
  ext x
  obtain ⟨P, hx⟩ := hf x
  let xP : P.carrier := ⟨x, hx⟩
  have hP : g.comp (T.comp P.carrier.subtype) =
      (T.comp P.carrier.subtype).comp P.restrict := by
    ext y
    exact LinearMap.congr_fun h y
  calc
    locallyFiniteSemisimplePart g hg (T x) =
        T (P.semisimpleMap xP) :=
      LinearMap.congr_fun (locallyFiniteSemisimplePart_intertwines_finite hg
        (T.comp P.carrier.subtype) hP) xP
    _ = T (locallyFiniteSemisimplePart f hf x) :=
      congrArg T (locallyFiniteSemisimplePart_eq f hf P xP).symm

/-- The complementary global component. -/
def locallyFiniteNilpotentPart (f : End k V) (hf : IsLocallyFinite f) : End k V :=
  f - locallyFiniteSemisimplePart f hf

/-- The complementary component kills each vector after some power. -/
theorem locallyFiniteNilpotentPart_locally_nilpotent
    (f : End k V) (hf : IsLocallyFinite f) (x : V) :
    ∃ n : ℕ, ((locallyFiniteNilpotentPart f hf) ^ n) x = 0 := by
  obtain ⟨P, hx⟩ := hf x
  let xP : P.carrier := ⟨x, hx⟩
  obtain ⟨n, hn⟩ := (jordanSemisimplePart_properties P.restrict).2.1
  have hP : (locallyFiniteNilpotentPart f hf).comp P.carrier.subtype =
      P.carrier.subtype.comp (jordanNilpotentPart P.restrict) := by
    ext y
    change f y - locallyFiniteSemisimplePart f hf y =
      f y - P.semisimpleMap y
    rw [locallyFiniteSemisimplePart_eq f hf P y]
  refine ⟨n, ?_⟩
  have hpow := LinearMap.congr_fun (Module.End.commute_pow_left_of_commute hP n) xP
  simpa only [LinearMap.comp_apply, hn, LinearMap.zero_apply, map_zero,
    xP, Submodule.subtype_apply] using hpow

/-- The original endomorphism commutes with its global semisimple component. -/
theorem locallyFiniteSemisimplePart_commute (f : End k V) (hf : IsLocallyFinite f) :
    Commute f (locallyFiniteSemisimplePart f hf) :=
  (locallyFiniteSemisimplePart_intertwines hf hf f rfl).symm

/-- The two compatible global components commute. -/
theorem locallyFiniteJordanParts_commute (f : End k V) (hf : IsLocallyFinite f) :
    Commute (locallyFiniteNilpotentPart f hf) (locallyFiniteSemisimplePart f hf) :=
  (locallyFiniteSemisimplePart_commute f hf).sub_left (Commute.refl _)

end Langlands.LinearAlgebra
