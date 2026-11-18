import Langlands.BushnellKutzko.UnitFiltration
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Tame corestrictions (Bushnell–Kutzko 1993, (1.3.3), printed p. 29)

The ring-and-field parameters also allow the same definition over an extension field, with
its ring of integers as constructed in `SubfieldIntegers`.
-/

namespace Langlands.BushnellKutzko

universe uO uK uE uV

variable (O : Type uO) (K : Type uK) (E : Type uE) (V : Type uV)
  [CommRing O] [Field K] [Algebra O K] [Field E] [Algebra K E]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  [Module E V] [IsScalarTower K E V]

/-- A tame corestriction `A → B` relative to `E/K`, where `A = End_K(V)` and
`B = End_E(V)`: an additive `(B,B)`-bimodule map whose image of every hereditary
`O`-order normalized by `Eˣ` is its intersection with `B` (BK93 (1.3.3), p. 29). -/
structure TameCorestriction extends Module.End K V →+ Module.End E V where
  /-- Compatibility with left multiplication by `B`. -/
  map_mul_left : ∀ (b : Module.End E V) (x : Module.End K V),
    toFun (b.restrictScalars K * x) = b * toFun x
  /-- Compatibility with right multiplication by `B`. -/
  map_mul_right : ∀ (x : Module.End K V) (b : Module.End E V),
    toFun (x * b.restrictScalars K) = toFun x * b
  /-- The defining order-image property, for every normalized hereditary order. -/
  image_order : ∀ 𝓛 : LatticeChain O K V,
    (∀ a : Eˣ, subfieldUnits K E V a ∈ 𝓛.stabilizer) →
      toFun '' (𝓛.order : Set (Module.End K V)) =
        {b : Module.End E V | b.restrictScalars K ∈ 𝓛.order}

instance : CoeFun (TameCorestriction O K E V)
    (fun _ => Module.End K V → Module.End E V) :=
  ⟨fun s => s.toAddMonoidHom⟩

end Langlands.BushnellKutzko
