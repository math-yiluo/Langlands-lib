/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

import WeilConjectures.AlgebraicGeometry.Curve.RootTrivializationBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.KummerBaseChangeCompatibility

/-!
# Kummer naturality in primitive-root coordinates

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, Kummer naturality in the proper and affine
cases (blueprint: lem-sc-constant-kummer-naturality).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance,
proof of proposition-cohomology-smooth-affine-curve, Kummer naturality in the proper and affine
cases (blueprint: lem-sc-constant-kummer-naturality).

Proof: the primitive-root sheaf map sends an integer class a to the power ζ^a. Pulling this
section back sends it to (algebraMap k K ζ)^a; thus the two trivializations commute with the
roots-of-unity pullback. Apply cohomology to this square. Use the inclusion square in
kummer_base_change_compatibility and its identification of Gm degree-one pullback with
Picard pullback to obtain the first equation. Naturality of the Kummer connecting maps in
degrees zero and one gives the Picard-boundary and units-boundary equations. Transport them
through the inverse trivializations. The prescribed homomorphisms determine t and tK
uniquely, so the equations hold for any equivalences satisfying ht and htK. The units
identity holds even without affineness; restrict it to the affine clause requested here.
The n = 1 case has zero roots-of-unity cohomology, hence also satisfies all equations. -/
theorem IsConnectedCurve.constant_kummer_baseChange_naturality
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    (n : ℕ) [NeZero n] (hn : (n : k) ≠ 0)
    (r : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q →+
        Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q)
    (hr : (∀ q : ℕ, r q =
        (Sheaf.H.map (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))).app
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom) q).comp
          (Etale.cohomologyMap
            (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (C.constantZMod n) q)))
    (ζ : k) (hζ : IsPrimitiveRoot ζ n)
    (hζK : IsPrimitiveRoot (algebraMap k K ζ) n)
    (t : ∀ q : ℕ, Sheaf.H (C.constantZMod n) q ≃+
          Sheaf.H (C.rootsOfUnitySheaf n) q)
        (tK : ∀ q : ℕ,
          Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).constantZMod n) q ≃+
          Sheaf.H
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).rootsOfUnitySheaf n) q)
    (ht : (∀ q : ℕ, (t q).toAddMonoidHom =
          Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q))
    (htK : (∀ q : ℕ, (tK q).toAddMonoidHom = Sheaf.H.map
          ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))).constantZModIsoRootsOfUnitySheaf n
              (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) hζK).hom q)) :
    (∀ x : Sheaf.H (C.constantZMod n) 1,
          Scheme.Pic.toCohomologicalPicardGroupAddEquiv
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
            (Additive.ofMul (Scheme.Pic.map
              (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
              ((Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm
                (Sheaf.H.map (kernel.ι (n • 𝟙 C.gmSheaf)) 1 (t 1 x))).toMul)) =
          Sheaf.H.map (kernel.ι (n • 𝟙
            (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).gmSheaf)) 1
              (tK 1 (r 1 x))) ∧
        (∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (L : Additive C.Pic),
          r 2 ((t 2).symm (C.kummerδ₁ n hnC
            (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
          (tK 2).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₁ n hnK
              (Scheme.Pic.toCohomologicalPicardGroupAddEquiv
                (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
                (Additive.ofMul (Scheme.Pic.map
                  (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L.toMul))))) ∧
    (IsAffine C → ∀ (hnC : IsUnit (n : Γ(C, ⊤)))
          (hnK : IsUnit (n : Γ(pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))), ⊤))) (a : Additive Γ(C, ⊤)ˣ),
          r 1 ((t 1).symm (C.kummerδ₀ n hnC a)) =
          (tK 1).symm
            ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).kummerδ₀ n hnK
              (Additive.ofMul (Units.map
                (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop.hom
                a.toMul)))) := by
  obtain ⟨hC, hP, φ, hφ₂, hφ₃, hδ, hι, _, hPic, hUnits, _⟩ :=
    kummer_base_change_compatibility k K C f (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
      K)))) (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) n hn
  have hθ := constant_root_trivialization_baseChange f n ζ hζ hζK φ hφ₂
  have ht_apply (q : ℕ) (x : Sheaf.H (C.constantZMod n) q) :
      t q x = Sheaf.H.map (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom q x :=
    congrArg (fun h => h x) (ht q)
  have htK_apply (q : ℕ) (x : Sheaf.H ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
    K)))).constantZMod n) q) :
      tK q x = Sheaf.H.map ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k
        K)))).constantZModIsoRootsOfUnitySheaf n (pullback.snd f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))) hζK).hom q x :=
    congrArg (fun h => h x) (htK q)
  have hsquare (q : ℕ) (x : Sheaf.H (C.constantZMod n) q) :
      tK q (r q x) = Sheaf.H.map φ.τ₁ q
        (Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          (C.rootsOfUnitySheaf n) q (t q x)) := by
    rw [htK_apply, hr, AddMonoidHom.comp_apply, ← Sheaf.H.map_comp_apply,
      ← hθ, Sheaf.H.map_comp_apply]
    exact congrArg (Sheaf.H.map φ.τ₁ q)
      ((Etale.cohomologyMap_map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) q
        (C.constantZModIsoRootsOfUnitySheaf n f hζ).hom x).symm.trans
          (congrArg (Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k
            K)))) (C.rootsOfUnitySheaf n) q)
            (ht_apply q x).symm))
  refine ⟨?_, ?_, ?_⟩
  · intro x
    let L := (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C).symm
      (Sheaf.H.map (kernel.ι (n • 𝟙 C.gmSheaf)) 1 (t 1 x))
    have hp := hPic L.toMul
    change Scheme.Pic.toCohomologicalPicardGroupAddEquiv (pullback f (Spec.map (CommRingCat.ofHom
      (algebraMap k K))))
      (Additive.ofMul (Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k
        K)))) L.toMul)) =
      Sheaf.H.map (upperStarGmSheafToGmSheaf (pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap k K))))) 1
        (Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          C.gmSheaf 1
          (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L)) at hp
    dsimp only [L] at hp
    rw [AddEquiv.apply_symm_apply] at hp
    refine hp.trans ?_
    rw [hsquare]
    have hi := hι 1 (t 1 x)
    rw [hφ₂] at hi
    convert hi using 1 <;> rfl
  · intro hnC hnK L
    apply (tK 2).injective
    rw [hsquare, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    change Sheaf.H.map φ.τ₁ 2
      (Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (C.rootsOfUnitySheaf n) 2
        (Sheaf.H.δSucc hC 1 (Scheme.Pic.toCohomologicalPicardGroupAddEquiv C L))) =
      Sheaf.H.δSucc hP 1 (Scheme.Pic.toCohomologicalPicardGroupAddEquiv (pullback f (Spec.map
        (CommRingCat.ofHom (algebraMap k K))))
        (Additive.ofMul (Scheme.Pic.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k
          K)))) L.toMul)))
    rw [hδ 1, hφ₃]
    exact congrArg (Sheaf.H.δSucc hP 1) (hPic L.toMul).symm
  · intro _ hnC hnK a
    apply (tK 1).injective
    rw [hsquare, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
    let z := (Sheaf.H.equiv₀ C.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale C)).symm (ULift.up a)
    have hz : C.kummerδ₀ n hnC a = Sheaf.H.δSucc hC 0 z := by
      have he := (Sheaf.H.equiv₀ C.gmSheaf
        (MorphismProperty.Over.mkIdTerminal @Etale C)).apply_symm_apply (ULift.up a)
      have hd := Sheaf.H.δSucc_zero hC
        (MorphismProperty.Over.mkIdTerminal @Etale C) z
      change Sheaf.H.δSections (C.kummerSequence_shortExact n hnC)
        (MorphismProperty.Over.mkIdTerminal @Etale C) (ULift.up a) = _
      change Sheaf.H.δSucc hC 0 z =
        Sheaf.H.δSections hC (MorphismProperty.Over.mkIdTerminal @Etale C)
          (Sheaf.H.equiv₀ C.gmSheaf
            (MorphismProperty.Over.mkIdTerminal @Etale C) z) at hd
      exact (hd.trans (congrArg
        (Sheaf.H.δSections hC (MorphismProperty.Over.mkIdTerminal @Etale C)) he)).symm
    rw [hz, hδ 0, hφ₃]
    have hu := hUnits a.toMul
    have hd := Sheaf.H.δSucc_zero hP
      (MorphismProperty.Over.mkIdTerminal @Etale (pullback f (Spec.map (CommRingCat.ofHom
        (algebraMap k K)))))
      (Sheaf.H.map (upperStarGmSheafToGmSheaf (pullback.fst f (Spec.map (CommRingCat.ofHom
        (algebraMap k K))))) 0
        (Etale.cohomologyMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
          C.gmSheaf 0 z))
    exact hd.trans (congrArg
      (Sheaf.H.δSections hP (MorphismProperty.Over.mkIdTerminal @Etale (pullback f (Spec.map
        (CommRingCat.ofHom (algebraMap k K)))))) hu)

end AlgebraicGeometry
