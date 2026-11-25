/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
import WeilConjectures.AlgebraicGeometry.Morphisms.NoetherianFiniteEtaleExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.NoetherianSpreadingData

/-!
# Underlying finite étale extension of a generically split Galois cover

## References

* Stacks Project, Tags 0EYJ and 0EZJ, proofs of the spreading theorem
* Stacks Project, Tags 0EYJ and 0EZJ, the construction of the finite étale morphism
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The underlying finite étale cover extends; no action on the extension is supplied. -/
theorem GaloisCover.exists_finiteEtale_extension {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (P : Scheme.{u}) (π : P ⟶ C) (ψ : Z.P ⟶ P),
      IsFinite π ∧ Etale π ∧ Surjective π ∧ IsPullback ψ Z.π π j := by
  obtain ⟨S₀, C₀, hI₀, c₀, σ₀, Cη₀, q₀, j₀, sη₀, Z₀, a, k, χ,
    hN₀, hQS₀, hS₀, hQC₀, hQSC₀, hSm₀, hGC₀, hσ₀, hG₀, hCη₀,
    hsq₀, hsj₀, hZ₀, hkj, hχ⟩ :=
    GaloisCover.exists_noetherian_spreading_data hS c σ hσ G hG q j hCη sη hsq hsj Z hZ
  let : IsIntegral S₀ := hI₀
  let : IsNoetherian S₀ := hN₀
  let : QuasiSeparatedSpace S₀ := hQS₀
  let : QuasiCompact c₀ := hQC₀
  let : QuasiSeparated c₀ := hQSC₀
  let : Smooth c₀ := hSm₀
  let : GeometricallyConnected c₀ := hGC₀
  obtain ⟨P₀, π₀, ψ₀, hFin₀, hEt₀, hψ₀⟩ :=
    GaloisCover.exists_finiteEtale_extension_noetherian hS₀ c₀ σ₀ hσ₀ G hG₀
      q₀ j₀ hCη₀ sη₀ hsq₀ hsj₀ Z₀ hZ₀
  let : IsFinite π₀ := hFin₀
  let : Etale π₀ := hEt₀
  have houter : IsPullback (χ ≫ ψ₀) Z.π π₀ (j ≫ a) := by
    simpa only [hkj] using hχ.paste_horiz hψ₀
  have hbase := IsPullback.of_hasPullback π₀ a
  let ψ := hbase.lift (χ ≫ ψ₀) (Z.π ≫ j) (by rw [houter.w, Category.assoc])
  have hψ : IsPullback ψ Z.π (Limits.pullback.snd π₀ a) j := houter.of_right' hbase
  have : ConnectedSpace C := GeometricallyConnected.connectedSpace c c.isOpenMap
  have : Nonempty ↥(Limits.pullback π₀ a) := by
    obtain ⟨z, hz⟩ := hZ
    exact ⟨(z ≫ ψ) (genericPoint (Spec S.functionField))⟩
  have : Surjective (Limits.pullback.snd π₀ a) := by
    constructor
    apply Set.range_eq_univ.mp
    exact IsClopen.eq_univ
      ⟨(Limits.pullback.snd π₀ a).isClosedMap.isClosed_range,
        (Limits.pullback.snd π₀ a).isOpenMap.isOpen_range⟩ (Set.range_nonempty _)
  exact ⟨Limits.pullback π₀ a, Limits.pullback.snd π₀ a, ψ, inferInstance, inferInstance,
    inferInstance, hψ⟩

end AlgebraicGeometry.Scheme
