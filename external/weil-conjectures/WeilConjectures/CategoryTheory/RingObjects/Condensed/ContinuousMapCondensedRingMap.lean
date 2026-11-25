/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement

/-!
# Functoriality of continuous-map condensed rings

Source: blueprint `sec-proetale-coefficients/sk-def-sfb-condensed-ring/`
`def-sfb-continuous-map-condensed-ring-map.md` and its proof
(blueprint: def-sfb-continuous-map-condensed-ring-map).

Postcomposition on the recorded universe-polymorphic continuous-map sheaves.
The coefficient rings lie in an arbitrary common universe, independent of the
universe of the profinite sets. The underlying ring objects and their tensor are
exactly those of `proposition-pro-etale-site-separably-closed--3`.
-/

@[expose] public section

universe u v

open CategoryTheory Opposite

namespace Profinite

variable {T T' : Type v} [TopologicalSpace T] [Ring T] [IsTopologicalRing T]
  [TopologicalSpace T'] [Ring T'] [IsTopologicalRing T']
  (φ : T →+* T') (hφ : Continuous φ)

/-- Postcomposition by a continuous ring homomorphism on the presheaves C(-,T).
Source: blueprint `def-sfb-continuous-map-condensed-ring-map.md`, displayed formula
(blueprint: def-sfb-continuous-map-condensed-ring-map). -/
noncomputable def continuousMapRingPresheafMapOfUniverse :
    continuousMapRingPresheafOfUniverse.{u, v} T ⟶
      continuousMapRingPresheafOfUniverse T' where
  app _ := RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((φ.compLeftContinuous _ hφ).comp ULift.ringEquiv.toRingHom))
  naturality _ _ _ := rfl

/-- The canonical morphism of condensed rings induced by postcomposition.
Source: blueprint `def-sfb-continuous-map-condensed-ring-map.md`, sheaf morphism
(blueprint: def-sfb-continuous-map-condensed-ring-map). -/
noncomputable def continuousMapRingSheafMapOfUniverse :
    continuousMapRingSheafOfUniverse.{u, v} T ⟶ continuousMapRingSheafOfUniverse T' :=
  ⟨continuousMapRingPresheafMapOfUniverse φ hφ⟩

/-- The underlying morphism of abelian sheaves of the continuous-map ring morphism.
Source: blueprint `def-sfb-continuous-map-condensed-ring-map.md`, ring-object clause
(blueprint: def-sfb-continuous-map-condensed-ring-map). -/
noncomputable def continuousMapRingObjMapOfUniverse :
    continuousMapRingObjOfUniverse.{u, v} T ⟶ continuousMapRingObjOfUniverse T' :=
  (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{max u v + 1} AddCommGrpCat.{max u v + 1})).map
      (continuousMapRingSheafMapOfUniverse φ hφ)

/-- Postcomposition is a morphism for the recorded canonical ring-object structures.
Source: blueprint `def-sfb-continuous-map-condensed-ring-map.proof.md`, part 3 citation
(blueprint: def-sfb-continuous-map-condensed-ring-map).

Proof: sectionwise postcomposition preserves all ring operations. Its naturality
is φ ∘ (a ∘ u) = (φ ∘ a) ∘ u. Both presheaves are the sheaves supplied by
`proposition-pro-etale-site-separably-closed--3`, so this gives a morphism of sheaves of rings.
Part 3 of `sk-def-sfb-ring-object`, specifically `Sheaf.isMonHom_sheafCompose_map`,
then makes its underlying abelian-sheaf map compatible with multiplication and unit.
The structures used here are the dependency's counit transports for its sheafified
tensor over the integers; no alternative ring-object structure is chosen. -/
theorem isMonHom_continuousMapRingObjMapOfUniverse :
    letI := (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
      (coherentTopology Profinite.{u})).monoidal
    letI := continuousMapRingObjOfUniverseMonObj.{u, v} T
    letI := continuousMapRingObjOfUniverseMonObj.{u, v} T'
    IsMonHom (continuousMapRingObjMapOfUniverse.{u, v} φ hφ) := by
  let := (sfbSheafTensorStructure (A := AddCommGrpCat.{max u v + 1})
    (coherentTopology Profinite.{u})).monoidal
  let := continuousMapRingObjOfUniverseMonObj.{u, v} T
  let := continuousMapRingObjOfUniverseMonObj.{u, v} T'
  change IsMonHom ((sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{max u v + 1} AddCommGrpCat.{max u v + 1})).map
      (continuousMapRingSheafMapOfUniverse φ hφ))
  exact Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u})
    (continuousMapRingSheafMapOfUniverse φ hφ)

end Profinite
