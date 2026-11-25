/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison

/-! # Coefficient transport for the ordinary derived tensor comparison

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change.
(blueprint: lem-pc-base-derived-tensor-ordinary-ring-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat


private theorem exists_tensorRingEquiv
    {R₀ A₀ B₀ R A B : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀]
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra R A] [Algebra R B]
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom) :
    ∃ eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B),
      ∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b := by
  have hRA' : eA.symm.toRingHom.comp (algebraMap R A) =
      (algebraMap R₀ A₀).comp eR.symm.toRingHom := by
    ext r
    apply eA.injective
    simpa using (RingHom.congr_fun hRA (eR.symm r)).symm
  have hRB' : eB.symm.toRingHom.comp (algebraMap R B) =
      (algebraMap R₀ B₀).comp eR.symm.toRingHom := by
    ext r
    apply eB.injective
    simpa using (RingHom.congr_fun hRB (eR.symm r)).symm
  let f := Algebra.TensorProduct.mapRingHom eR.toRingHom eA.toRingHom eB.toRingHom
    hRA hRB
  let g := Algebra.TensorProduct.mapRingHom eR.symm.toRingHom eA.symm.toRingHom
    eB.symm.toRingHom hRA' hRB'
  have hgf (x : A₀ ⊗[R₀] B₀) : g (f x) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [f, g]
    | add x y hx hy => simp [hx, hy]
  have hfg (x : A ⊗[R] B) : f (g x) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul a b => simp [f, g]
    | add x y hx hy => simp [hx, hy]
  let e : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B) :=
    { __ := f
      invFun := g
      left_inv := hgf
      right_inv := hfg }
  exact ⟨e, fun a b ↦ Algebra.TensorProduct.mapRingHom_tmul
    eR.toRingHom eA.toRingHom eB.toRingHom hRA hRB a b⟩

private theorem exists_extensionIso
    {S₀ S D₀ D : Type u}
    [CommRing S₀] [CommRing S] [CommRing D₀] [CommRing D]
    (f₀ : S₀ →+* D₀) (f : S →+* D)
    (eS : S₀ ≃+* S) (eD : D₀ ≃+* D)
    (hf : eD.toRingHom.comp f₀ = f.comp eS.toRingHom)
    (P₀ : ModuleCat.{u} S₀) (P : ModuleCat.{u} S)
    (k : P₀ ≅ (restrictScalars.{u} eS.toRingHom).obj P) :
    ∃ l : (extendScalars f₀).obj P₀ ≅
        (restrictScalars.{u} eD.toRingHom).obj ((extendScalars f).obj P),
      ∀ (d : D₀) (p : P₀), l.hom (d ⊗ₜ[S₀, f₀] p) =
        eD d ⊗ₜ[S, f] (show P from k.hom p) := by
  let : Module S₀ D₀ := Module.compHom D₀ f₀
  let : Module S D := Module.compHom D f
  have : RingHomInvPair eS.toRingHom eS.symm.toRingHom :=
    RingHomInvPair.of_ringEquiv eS
  have : RingHomInvPair eS.symm.toRingHom eS.toRingHom :=
    RingHomInvPair.of_ringEquiv_symm eS
  let c : LinearEquiv eS.toRingHom (σ' := eS.symm.toRingHom) D₀ D :=
    { __ := eD.toAddEquiv
      map_smul' := by
        intro r d
        change eD (f₀ r * d) = f (eS r) * eD d
        rw [map_mul]
        exact congrArg (fun z ↦ z * eD d) (RingHom.congr_fun hf r) }
  let h : LinearEquiv eS.toRingHom (σ' := eS.symm.toRingHom) P₀ P :=
    { __ := k.toLinearEquiv.toAddEquiv
      map_smul' := fun r p ↦ (k.hom.hom.map_smul r p) }
  let v := TensorProduct.congr c h
  let l : (extendScalars f₀).obj P₀ ≃ₗ[D₀]
      (restrictScalars.{u} eD.toRingHom).obj ((extendScalars f).obj P) :=
    { __ := v.toAddEquiv
      map_smul' := by
        intro d z
        change v (d • z) = eD d • v z
        induction z using TensorProduct.inductionOn with
        | tmul d' p =>
          change v ((d * (show D₀ from d')) ⊗ₜ[S₀, f₀] p) =
            eD d • v (d' ⊗ₜ[S₀, f₀] p)
          rw [TensorProduct.congr_tmul, TensorProduct.congr_tmul]
          change eD (d * (show D₀ from d')) ⊗ₜ[S, f] (show P from k.hom p) = _
          rw [map_mul]
          rfl
        | add z w hz hw =>
          change v (d • (z + w)) = eD d • v (z + w)
          rw [smul_add, map_add, map_add, hz, hw, smul_add] }
  exact ⟨l.toModuleIso, fun d p ↦ TensorProduct.congr_tmul c h d p⟩

private theorem exists_extensionComplexIso
    {S₀ S D₀ D : Type u}
    [CommRing S₀] [CommRing S] [CommRing D₀] [CommRing D]
    (f₀ : S₀ →+* D₀) (f : S →+* D)
    (eS : S₀ ≃+* S) (eD : D₀ ≃+* D)
    (hf : eD.toRingHom.comp f₀ = f.comp eS.toRingHom)
    (Q₀ : CochainComplex (ModuleCat.{u} S₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ)
    (q : Q₀ ≅ ((restrictScalars.{u} eS.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q) :
    ∃ s : ((extendScalars f₀).mapHomologicalComplex (.up ℤ)).obj Q₀ ≅
        ((restrictScalars.{u} eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
          (((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q),
      ∀ (j : ℤ) (d : D₀) (x : Q₀.X j),
        s.hom.f j (d ⊗ₜ[S₀, f₀] x) =
          eD d ⊗ₜ[S, f] (show Q.X j from q.hom.f j x) := by
  classical
  choose l hl using fun j ↦ exists_extensionIso f₀ f eS eD hf (Q₀.X j) (Q.X j)
    (HomologicalComplex.Hom.isoApp q j)
  let s : ((extendScalars f₀).mapHomologicalComplex (.up ℤ)).obj Q₀ ≅
      ((restrictScalars.{u} eD.toRingHom).mapHomologicalComplex (.up ℤ)).obj
        (((extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q) :=
    HomologicalComplex.Hom.isoOfComponents l (by
    intro i j hij
    apply ExtendScalars.hom_ext
    intro x
    change (extendScalars f).map (Q.d i j) ((l i).hom ((1 : D₀) ⊗ₜ[S₀, f₀] x)) =
      (l j).hom ((extendScalars f₀).map (Q₀.d i j) ((1 : D₀) ⊗ₜ[S₀, f₀] x))
    rw [hl, ExtendScalars.map_tmul, ExtendScalars.map_tmul, hl]
    have hq := ConcreteCategory.congr_hom (q.hom.comm i j) x
    change Q.d i j (q.hom.f i x) = q.hom.f j (Q₀.d i j x) at hq
    change eD 1 ⊗ₜ[S, f] (Q.d i j (q.hom.f i x)) =
      eD 1 ⊗ₜ[S, f] (show Q.X j from q.hom.f j (Q₀.d i j x))
    rw [hq])
  exact ⟨s, hl⟩

/-- Transport the ordinary comparison, before extension to the fourth ring.

Proof: compatible eR, eA and eB induce a tensor-ring isomorphism eE, sending
 a tensor b to eA(a) tensor eB(b). Tensoring the input isomorphism gives s,
with the stated generator formula. Restriction along eR and eB gives exact
inverse equivalences on module, homotopy and derived categories. If the chosen
derived categories have different morphism universes, use their localization
universal properties to identify the two category-of-fractions presentations.
Transport M's universal left-derived functor and counit through these
 equivalences. Uniqueness of universal left-derived functors identifies the
result with N's functor, compatibly with the counits. Apply homology and conjugate
by cohomologyIso to obtain the cohomology isomorphism k. Naturality for
multiplication by a and cohomologyIso_smul give eA-semilinearity; B-linearity
gives eB-semilinearity. Tensor induction gives eE-semilinearity, for both k and
its inverse. The comparison_eq identities, counit compatibility and homology
naturality at s give the displayed ordinary comparison square. The ordinaryIso
maps are identified on generators by ordinaryIso_tmul. Neither localizedComparison
nor ordinaryToLocalized occurs in this conclusion. Zero rings and zero complexes
are allowed; no flatness or invertibility of comparisons is used.
Source: Stacks Project, Tag 06Y6, lemma-derived-base-change, independence of
choices and derived change of rings; the two-universe formulation uses
localization uniqueness.
(blueprint: lem-pc-base-derived-tensor-ordinary-ring-comparison). -/
theorem exists_baseDerivedTensor_ordinary_ring_comparison
    {R₀ A₀ B₀ C₀ R A B C : Type u}
    [CommRing R₀] [CommRing A₀] [CommRing B₀] [CommRing C₀]
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R₀ A₀] [Algebra R₀ B₀] [Algebra (A₀ ⊗[R₀] B₀) C₀]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₀)]
    [HasDerivedCategory.{w} (ModuleCat.{u} B₀)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w'} (ModuleCat.{u} B)]
    (Q₀ : CochainComplex (ModuleCat.{u} A₀) ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (M : BaseDerivedTensorCohomologyModel R₀ A₀ B₀ Q₀ C₀)
    (N : BaseDerivedTensorCohomologyModel R A B Q C)
    (eR : R₀ ≃+* R) (eA : A₀ ≃+* A) (eB : B₀ ≃+* B)
    (hRA : eA.toRingHom.comp (algebraMap R₀ A₀) =
      (algebraMap R A).comp eR.toRingHom)
    (hRB : eB.toRingHom.comp (algebraMap R₀ B₀) =
      (algebraMap R B).comp eR.toRingHom)
    (q : Q₀ ≅ ((restrictScalars.{u} eA.toRingHom).mapHomologicalComplex (.up ℤ)).obj Q)
    (i : ℤ) :
    let K₀ := ((extendScalars (algebraMap A₀ (A₀ ⊗[R₀] B₀))).mapHomologicalComplex
      (.up ℤ)).obj Q₀
    let K := ((extendScalars (algebraMap A (A ⊗[R] B))).mapHomologicalComplex
      (.up ℤ)).obj Q
    ∃ (eE : (A₀ ⊗[R₀] B₀) ≃+* (A ⊗[R] B)),
      (∀ (a : A₀) (b : B₀), eE (a ⊗ₜ[R₀] b) = eA a ⊗ₜ[R] eB b) ∧
      ∃ (s : K₀ ≅ ((restrictScalars.{u} eE.toRingHom).mapHomologicalComplex
          (.up ℤ)).obj K)
        (k : M.cohomology i ≅ (restrictScalars.{u} eE.toRingHom).obj (N.cohomology i)),
        (∀ (j : ℤ) (r : A₀ ⊗[R₀] B₀) (x : Q₀.X j),
          s.hom.f j (r ⊗ₜ[A₀, algebraMap A₀ (A₀ ⊗[R₀] B₀)] x) =
            eE r ⊗ₜ[A, algebraMap A (A ⊗[R] B)] (show Q.X j from q.hom.f j x)) ∧
        k.hom ≫ (restrictScalars.{u} eE.toRingHom).map (N.comparison i) ≫
            ((K.sc i).mapHomologyIso (restrictScalars.{u} eE.toRingHom)).inv =
          M.comparison i ≫ HomologicalComplex.homologyMap s.hom i := by
  obtain ⟨eE, heE⟩ := exists_tensorRingEquiv eR eA eB hRA hRB
  have hAE : eE.toRingHom.comp (algebraMap A₀ (A₀ ⊗[R₀] B₀)) =
      (algebraMap A (A ⊗[R] B)).comp eA.toRingHom := by
    ext a
    change eE (a ⊗ₜ[R₀] (1 : B₀)) = eA a ⊗ₜ[R] (1 : B)
    rw [heE, map_one]
  obtain ⟨s, hs⟩ := exists_extensionComplexIso
    (algebraMap A₀ (A₀ ⊗[R₀] B₀)) (algebraMap A (A ⊗[R] B)) eA eE hAE Q₀ Q q
  obtain ⟨kB, hA, hsquare⟩ := exists_baseDerivedTensor_restricted_ring_comparison
    Q₀ Q M N eR eA eB hRA hRB q eE heE s hs i
  let v : M.cohomology i ≃+ N.cohomology i := kB.toLinearEquiv.toAddEquiv
  have hB (b : B₀) (x : M.cohomology i) :
      v ((Algebra.TensorProduct.includeRight b : A₀ ⊗[R₀] B₀) • x) =
        (Algebra.TensorProduct.includeRight (eB b) : A ⊗[R] B) • v x := by
    exact kB.hom.hom.map_smul b x
  have hlinear (r : A₀ ⊗[R₀] B₀) (x : M.cohomology i) :
      v (r • x) = eE r • v x := by
    induction r using TensorProduct.inductionOn with
    | tmul a b =>
      rw [heE]
      have ht₀ : (a ⊗ₜ[R₀] b : A₀ ⊗[R₀] B₀) =
          (Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) *
            Algebra.TensorProduct.includeRight b := by
        change a ⊗ₜ[R₀] b = (a ⊗ₜ[R₀] (1 : B₀)) * ((1 : A₀) ⊗ₜ[R₀] b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have ht : (eA a ⊗ₜ[R] eB b : A ⊗[R] B) =
          (Algebra.TensorProduct.includeLeft (S := R) (eA a) : A ⊗[R] B) *
            (Algebra.TensorProduct.includeRight (eB b) : A ⊗[R] B) := by
        change eA a ⊗ₜ[R] eB b =
          (eA a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] eB b)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [ht₀, ht, mul_smul, mul_smul]
      change v ((Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) •
        ((Algebra.TensorProduct.includeRight b : A₀ ⊗[R₀] B₀) • x)) = _
      rw [show v ((Algebra.TensorProduct.includeLeft (S := R₀) a : A₀ ⊗[R₀] B₀) •
          ((Algebra.TensorProduct.includeRight b : A₀ ⊗[R₀] B₀) • x)) =
        (Algebra.TensorProduct.includeLeft (S := R) (eA a) : A ⊗[R] B) •
          v ((Algebra.TensorProduct.includeRight b : A₀ ⊗[R₀] B₀) • x) from hA a _, hB]
    | add r t hr ht => simp only [add_smul, map_add, hr, ht]
  let l : M.cohomology i ≃ₗ[A₀ ⊗[R₀] B₀]
      (restrictScalars.{u} eE.toRingHom).obj (N.cohomology i) :=
    LinearEquiv.ofBijective
      { toFun := fun x ↦
          (show (restrictScalars.{u} eE.toRingHom).obj (N.cohomology i) from v x)
        map_add' := v.map_add
        map_smul' := hlinear }
      v.bijective
  refine ⟨eE, heE, s, l.toModuleIso, hs, ?_⟩
  ext x
  exact hsquare x

end ModuleCat
