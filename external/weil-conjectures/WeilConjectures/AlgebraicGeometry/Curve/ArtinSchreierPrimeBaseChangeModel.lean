/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius

import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows

/-! # Prime-coefficient Artin--Schreier comparison under field extension -/

@[expose] public section

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

/-- If `0 → A → G → G → 0` is short exact, with second map `wp` surjective on `H⁰`, and `wp` acts on
`H¹(G) ≅ V` as `F - 1` for a `p`-linear `F`, then `H¹(A)` is identified with the fixed points of
`F`, compatibly with the map `H¹(A) → H¹(G)`. -/
theorem exists_fixedPoints_equiv_of_exact_row
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {X : Scheme.{u}} {A G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (i : A ⟶ G) (wp : G ⟶ G) (z : i ≫ wp = 0)
    (hS : (ShortComplex.mk i wp z).ShortExact)
    (hs : Function.Surjective (Sheaf.H.map wp 0))
    (V : Type (u + 1)) [AddCommGroup V] [Module k V]
    (F : V →ₛₗ[frobenius k p] V) (b : Sheaf.H G 1 ≃+ V)
    (hF : ∀ x, b (Sheaf.H.map wp 1 x) = F (b x) - b x) :
    ∃ e : Sheaf.H A 1 ≃+ LinearMap.Frobenius.fixedPoints F,
      ∀ x, (e x : V) = b (Sheaf.H.map i 1 x) := by
  classical
  have hδ : ∀ y, Sheaf.H.δSucc hS 0 y = 0 := by
    intro y
    exact ((Sheaf.H.exact_map_δSucc hS 0) y).2 (hs y)
  have hinj : Function.Injective (Sheaf.H.map i 1) := by
    apply (injective_iff_map_eq_zero _).2
    intro x hx
    obtain ⟨y, hy⟩ := ((Sheaf.H.exact_δSucc_map hS 0) x).1 hx
    exact hy.symm.trans (hδ y)
  have hfix (x : Sheaf.H A 1) :
      F (b (Sheaf.H.map i 1 x)) = b (Sheaf.H.map i 1 x) := by
    apply sub_eq_zero.mp
    rw [← hF]
    have hx := ((Sheaf.H.exact_map_map hS 1) (Sheaf.H.map i 1 x)).2 ⟨x, rfl⟩
    rw [hx, map_zero]
  let j : Sheaf.H A 1 →+ LinearMap.Frobenius.fixedPoints F :=
    { toFun x := ⟨b (Sheaf.H.map i 1 x), LinearMap.Frobenius.mem_fixedPoints.mpr (hfix x)⟩
      map_zero' := by apply Subtype.ext; simp
      map_add' x y := by apply Subtype.ext; simp }
  have hj : Function.Bijective j := by
    constructor
    · intro x y hxy
      apply hinj
      apply b.injective
      exact congrArg Subtype.val hxy
    · intro y
      have hy : Sheaf.H.map wp 1 (b.symm (y : V)) = 0 := by
        apply b.injective
        rw [hF, AddEquiv.apply_symm_apply, map_zero]
        exact sub_eq_zero.mpr (LinearMap.Frobenius.mem_fixedPoints.mp y.property)
      obtain ⟨x, hx⟩ := ((Sheaf.H.exact_map_map hS 1) (b.symm (y : V))).1 hy
      refine ⟨x, Subtype.ext ?_⟩
      change b (Sheaf.H.map i 1 x) = (y : V)
      rw [hx, AddEquiv.apply_symm_apply]
  exact ⟨AddEquiv.ofBijective j hj, fun _ ↦ rfl⟩

/-- Prime-coefficient first cohomology is the Frobenius kernel, naturally under base change.
Source: Stacks Project, Tag 0A3P, proof, and Tag 02KH, flat base change.
(blueprint: proposition-p-torsion-smooth-proper-curve--2)

Proof: Use H¹(C,O_C) as V, with its scalar action and finite-dimensionality from proper
coherent cohomology and the étale/Zariski quasi-coherent comparison. The sectionwise
p-th power map induces a p-semilinear endomorphism F: the identity
(cx)^p = c^p x^p gives semilinearity after applying additive cohomology. Apply the
Artin--Schreier long exact sequence. Its degree-zero F-1 map is onto by the proper
degree-zero theorem, so the next map identifies H¹(C,Z/p) with ker(F-1). Transport
this identification through the natural Ext/derived comparison. Flat base change gives
H¹(C',O_C') = k' tensor V. Transport its Frobenius across this linear equivalence to F'.
The p-th power maps commute with pullback of functions, giving the displayed tensor
identity. Naturality of the connecting sequence then identifies cohomology pullback
with v mapping to 1 tensor v on kernels. No invariance of kernels is used. For a
connected smooth curve of dimension zero, it is Spec k, and coherent H¹ vanishes;
the same sequence makes both degree-one groups zero, giving V = 0. Thus the
exact-dimension-one scalar-model theorem is only used in the dimension-one case. -/
theorem exists_constantZMod_one_frobenius_baseChange_model
    {k k' : Type u}
    [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k'] [Algebra k k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [IsCurve f] [Smooth f] [ConnectedSpace C] [IsProper f]
    (p : ℕ) [Fact p.Prime] [CharP k p] [CharP k' p]
    {C' : Scheme.{u}} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C}
    (h : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :
    ∃ (V : ModuleCat.{u + 1} k) (_ : FiniteDimensional k V)
      (F : V →ₛₗ[frobenius k p] V)
      (F' : (k' ⊗[k] V) →ₛₗ[frobenius k' p] (k' ⊗[k] V))
      (hF' : ∀ v : V, F' (1 ⊗ₜ[k] v) = 1 ⊗ₜ[k] F v)
      (e : Sheaf.H (C.constantZMod p) 1 ≃+ LinearMap.Frobenius.fixedPoints F)
      (e' : Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} ι').obj
        (C.constantZMod p)) 1 ≃+ LinearMap.Frobenius.fixedPoints F'),
      ∀ x, e' (Etale.cohomologyMap ι' (C.constantZMod p) 1 x) =
        (⟨1 ⊗ₜ[k] (e x : V), by
          rw [LinearMap.Frobenius.mem_fixedPoints, hF',
            LinearMap.Frobenius.mem_fixedPoints.mp (e x).2]⟩ :
          LinearMap.Frobenius.fixedPoints F') := by
  obtain ⟨V, hV, F, F', hF', G, G', i, i', wp, wp', z, z', q, b, b',
    hS, hS', hs, hs', hsq, hF, hFmodel', hbc⟩ :=
    exists_artinSchreier_frobenius_exact_rows f p h
  obtain ⟨e, he⟩ := exists_fixedPoints_equiv_of_exact_row p i wp z hS hs V F b hF
  obtain ⟨e', he'⟩ :=
    exists_fixedPoints_equiv_of_exact_row p i' wp' z' hS' hs' (k' ⊗[k] V) F' b' hFmodel'
  refine ⟨V, hV, F, F', hF', e, e', ?_⟩
  intro x
  apply Subtype.ext
  change (e' (Etale.cohomologyMap ι' (C.constantZMod p) 1 x) : k' ⊗[k] V) =
    1 ⊗ₜ[k] (e x : V)
  rw [he', he, ← hsq, Sheaf.H.map_comp_apply, ← Etale.cohomologyMap_map]
  exact hbc (Sheaf.H.map i 1 x)

end AlgebraicGeometry.IsCurve
