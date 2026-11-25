/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.SmoothCurveConnectedCoproduct
import WeilConjectures.AlgebraicGeometry.FiniteCoproductConstantBaseChangeSquare
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly

/-! # Reduction of curve comparison to connected curves

Source: blueprint theorem-cohomology-curves--6, first step (clopen connected components).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Comparison on connected smooth curves implies comparison on every qc smooth
separated curve of relative dimension one.
Source: blueprint theorem-cohomology-curves--6, first step.
(blueprint: lem-sc-curve-cohomology-connected-reduction)

Proof: C is finite type over k and hence Noetherian. Its finitely many
connected components are clopen. Restricting f to each gives a separated,
finite type, smooth morphism of relative dimension one; its connected nonempty
source has dimension exactly one, so it is a connected smooth curve. The
components form a finite coproduct. Finite-coproduct cohomology assembly,
followed by the constant-sheaf restriction isomorphisms, gives bijective source
product coordinates. The base-change square theorem gives bijective target
product coordinates and identifies each coordinate with the component
comparison. Apply h componentwise. Equality of images implies equality in
every source coordinate, proving injectivity. For surjectivity, lift each target
coordinate through its component comparison and then through the source product
coordinates. The empty product handles C empty. No connectedness statement for
the base-changed components is required. -/
theorem bijective_curve_cohomologyMap_of_connected
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    (n q : ℕ)
    (h : ∀ {D : Scheme.{u}} (g : D ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g],
      Function.Bijective (Etale.cohomologyMap
        (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (D.constantZMod n) q)) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (C.constantZMod n) q) := by
  classical
  obtain ⟨I, hI, D, g, ι, hD, hw, ⟨hc⟩⟩ := exists_smoothCurveConnectedCoproduct f
  have : Finite I := hI
  let a (i : I) :=
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (ι i)).app
      (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))
  let t (i : I) : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (ι i)).obj
      (C.constantZMod n)) q ≃ Sheaf.H ((D i).constantZMod n) q :=
    { toFun := Sheaf.H.map (a i).hom q
      invFun := Sheaf.H.map (a i).inv q
      left_inv := fun x => by
        rw [← Sheaf.H.map_comp_apply, (a i).hom_inv_id, Sheaf.H.map_id_apply]
      right_inv := fun x => by
        rw [← Sheaf.H.map_comp_apply, (a i).inv_hom_id, Sheaf.H.map_id_apply] }
  let r := fun x : Sheaf.H (C.constantZMod n) q =>
    fun i : I => t i (Etale.cohomologyMap (ι i) (C.constantZMod n) q x)
  have hr : Function.Bijective r :=
    (Function.Bijective.piMap (fun i => (t i).bijective)).comp
      (Etale.finiteCoproductCohomologyAssembly D C ι hc (C.constantZMod n) q)
  let e := Equiv.ofBijective r hr
  obtain ⟨eK, he⟩ :=
    Etale.finiteCoproductConstantBaseChangeSquare (K := K) D f g ι hw hc n q
  have he' (x : Sheaf.H (C.constantZMod n) q) (i : I) :
      eK (Etale.cohomologyMap
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (C.constantZMod n) q x) i =
      Etale.cohomologyMap
        (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        ((D i).constantZMod n) q (e x i) := he x i
  have hb (i : I) : Function.Bijective (Etale.cohomologyMap
      (pullback.fst (g i) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      ((D i).constantZMod n) q) := by
    have : IsConnectedCurve (g i) := (hD i).1
    have : Smooth (g i) := (hD i).2
    exact h (g i)
  constructor
  · intro x y hxy
    apply e.injective
    funext i
    apply (hb i).1
    rw [← he' x i, ← he' y i, hxy]
  · intro y
    choose z hz using fun i => (hb i).2 (eK y i)
    refine ⟨e.symm z, eK.injective ?_⟩
    funext i
    rw [he', e.apply_symm_apply]
    exact hz i

end AlgebraicGeometry
