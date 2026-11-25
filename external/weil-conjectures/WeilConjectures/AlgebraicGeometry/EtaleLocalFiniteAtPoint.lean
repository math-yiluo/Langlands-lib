/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.FibreProductPointResidueField
import WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance.PropertyC
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# An isolated fibre point becomes finite after elementary étale base change

Source: Stacks Project, More on Morphisms, Lemma 02LK, clauses (a), (b), (i)-(iii)
(blueprint: lem-weil-pbc-etale-local-finite-at-point-elementary).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem spec_residueFieldMap_conjugate {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (q : Spec B) :
    (Scheme.Spec.residueFieldIso A (Spec.map φ q)).hom ≫
      CommRingCat.ofHom (Ideal.ResidueField.map (q.comap φ.hom).asIdeal q.asIdeal φ.hom rfl) ≫
      (Scheme.Spec.residueFieldIso B q).inv = (Spec.map φ).residueFieldMap q := by
  have h := congrArg (fun m => m ≫ (Scheme.Spec.residueFieldIso B q).inv)
    (Spec.residueFieldMap_residueFieldIso_hom φ q)
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Spec.map_apply] using h.symm

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_spec_residueFieldMap {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (p : Spec A) (q : Spec B) (hp : p = q.comap φ.hom)
    (hbij : Function.Bijective
      (Ideal.ResidueField.map p.asIdeal q.asIdeal φ.hom (congrArg PrimeSpectrum.asIdeal hp))) :
    IsIso ((Spec.map φ).residueFieldMap q) := by
  subst p
  rw [← spec_residueFieldMap_conjugate]
  let : IsIso (CommRingCat.ofHom
      (Ideal.ResidueField.map (q.comap φ.hom).asIdeal q.asIdeal φ.hom rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_pullback_fst_residueFieldMap {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso (g.residueFieldMap (pullback.snd f g z))] :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  let T := Scheme.Pullback.Triplet.ofPoint z
  have : IsIso (g.residueFieldMap T.y) := by
    change IsIso (g.residueFieldMap (pullback.snd f g z))
    infer_instance
  have : IsIso ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y) :=
    inferInstance
  have hinl : IsIso T.tensorInl := by
    change IsIso (pushout.inl
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    infer_instance
  let e := (asIso T.tensorInl).commRingCatIsoToRingEquiv
  have hfield : IsField T.tensor := e.symm.toMulEquiv.isField (Field.toIsField _)
  let := hfield.toField
  let ψ := (Scheme.Pullback.ofPointTensor z).hom
  let p := RingHom.ker ψ
  have hp : p = ⊥ := (RingHom.injective_iff_ker_eq_bot ψ).mp (RingHom.injective ψ)
  have hquot : IsField (T.tensor ⧸ p) := by
    rw [hp]
    exact (RingEquiv.quotientBot T.tensor).toMulEquiv.isField hfield
  obtain ⟨e', -, hl, -⟩ :=
    (Scheme.Pullback.exists_residueField_equiv_ofPointTensor f g z).2 hquot
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨RingHom.injective ((pullback.fst f g).residueFieldMap z).hom, ?_⟩
  change Function.Surjective ((pullback.fst f g).residueFieldMap z).hom
  rw [← hl]
  exact e'.surjective.comp
    ((Ideal.Quotient.mk_surjective).comp
      (ConcreteCategory.bijective_of_isIso T.tensorInl).2)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Stacks Project, Lemma 02LK, excluding its final persistence assertion
(blueprint: lem-weil-pbc-etale-local-finite-at-point-elementary).
An isolated fibre point of a locally finite type morphism admits an elementary étale
neighbourhood and a finite open piece with exactly one point over the distinguished base
point; that point lies over the original point with unchanged residue field.

Proof plan from the node:
1. Choose affine opens `x ∈ Y ⊆ X` and `f(Y) ⊆ W ⊆ S`, with `s ∈ W`, using
   `lem-weil-pbc-affine-open-spec-points`. The corresponding ring map `R → A` is finite type
   by `lem-weil-pbc-lft-affine-pairs`.
2. Use `f.fiberHomeo s` and the affine identifications to see that the prime corresponding
   to `x` is isolated among the primes of `A` over the prime corresponding to `s`.
3. Apply `lem-weil-pbc-etale-quasi-finite-finite-one-prime` (Stacks 00UJ) to obtain an étale
   algebra `R'`, a prime over `s` with unchanged residue field, and an idempotent `e` of
   `C = R' ⊗[R] A` whose localization is finite and has a unique prime over that base prime.
4. Put `U = Spec R'`. Its composite map to `W ⊆ S` is étale by
   `lem-weil-pbc-etale-ring-map-iff-etale-affine` and
   `definition-torsion-sheaves--3`. The residue-field identifications of
   `lem-weil-pbc-spec-residue-field-identification` give the elementary neighbourhood.
5. The lemmas `lem-weil-pbc-open-fibre-product`, `lem-weil-pbc-fibre-product-affine-spectra`
   and `lem-weil-pbc-principal-localization-open-immersion` identify `Spec Cₑ` with an open
   subscheme `V` of `X ×[S] U`, compatibly with both projections.
6. Apply `lem-weil-pbc-finite-local-on-target` to show `V → U` is finite.
7. The unique prime supplied in step 3 gives the unique point over `u` and maps to `x`.
8. Since `κ(s) → κ(u)` is an isomorphism, `κ(x) ⊗[κ(s)] κ(u)` is `κ(x)` and is a field.
   Its canonical map to the residue field of the pullback point is injective because its
   source is a field. Thus its kernel is zero. Apply
   `lem-weil-pbc-fibre-product-point-residue-field` to identify the tensor quotient with
   that residue field, compatibly with `κ(x)`. The open inclusion also induces a
   residue-field isomorphism, proving the assertion for `v`. -/
theorem exists_etale_finite_open_of_isolated_fiber_point
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (hx : IsOpen ({f.asFiber x} : Set (f.fiber (f x)))) :
    ∃ (U : Scheme.{u}) (φ : U ⟶ S) (u : U),
      Etale φ ∧ φ u = f x ∧ IsIso (φ.residueFieldMap u) ∧
      ∃ (V : (pullback f φ).Opens), IsFinite (V.ι ≫ pullback.snd f φ) ∧
        ∃ (v : V), (V.ι ≫ pullback.snd f φ) v = u ∧
          (∀ (w : V), (V.ι ≫ pullback.snd f φ) w = u → w = v) ∧
          (V.ι ≫ pullback.fst f φ) v = x ∧
          IsIso ((V.ι ≫ pullback.fst f φ).residueFieldMap v) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  change IsAffineOpen U at hU
  change IsAffineOpen V at hV
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr hx).quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', hres, _, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (TensorProduct Γ(S, U) R Γ(X, V))) ≅
      pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (TensorProduct Γ(S, U) R Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  have hgp : g ≫ pullback.fst f _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) ≫
        hV.fromSpec := by
    simp only [g, Category.assoc, pullback.map, pullback.lift_fst]
    rw [← Category.assoc, he₁]
  have hgq : g ≫ pullback.snd f _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (TensorProduct Γ(S, U) R Γ(X, V)))) := by
    dsimp [g, e₁, RingHom.algebraMap_toAlgebra, φ]
    simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id,
      pullbackSymmetry_hom_comp_snd]
    exact pullbackSpecIso_inv_fst Γ(S, U) R Γ(X, V)
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec (.of (Localization.Away e)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [Scheme.Hom.isoOpensRange, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  let u₀ : Spec (.of R) := ⟨P, ‹_›⟩
  let v₀ : W₁ := ⟨g ⟨P', ‹_›⟩, ⟨⟨P', ‹_›⟩, heP', rfl⟩⟩
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, u₀, inferInstance, ?_, ?_,
    W₁, ‹_›, v₀, ?_, ?_, ?_, ?_⟩
  · dsimp [u₀, Spec.map_apply]
    convert! hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    exact PrimeSpectrum.ext (Ideal.over_def _ _).symm
  · have : IsIso ((Spec.map φ).residueFieldMap u₀) :=
      isIso_spec_residueFieldMap φ (hU.primeIdealOf ⟨f x, hxU⟩) u₀
        (PrimeSpectrum.ext (P.over_def _)) hres
    rw [Scheme.residueFieldMap_comp]
    infer_instance
  · change (g ≫ pullback.snd f _) ⟨P', ‹_›⟩ = u₀
    rw [hgq]
    exact PrimeSpectrum.ext (P'.over_def P).symm
  · intro w hw
    obtain ⟨Q, heQ, hQ⟩ := w.property
    change g Q = w.val at hQ
    have hQP : Q.asIdeal.LiesOver P := by
      constructor
      have hh : (Spec.map (CommRingCat.ofHom
          (algebraMap R (TensorProduct Γ(S, U) R Γ(X, V))))) Q = u₀ := by
        rw [← hgq, Scheme.Hom.comp_apply, hQ]
        exact hw
      exact (congrArg PrimeSpectrum.asIdeal hh).symm
    have hQQ : Q = ⟨P', ‹_›⟩ := PrimeSpectrum.ext
      (huniq Q.asIdeal Q.isPrime hQP heQ)
    apply Subtype.ext
    change w.val = g ⟨P', ‹_›⟩
    rw [← hQ, hQQ]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · change (g ≫ pullback.fst f _) ⟨P', ‹_›⟩ = _
      rw [hgp]
      rfl
    convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  · have : IsIso ((Spec.map φ).residueFieldMap u₀) :=
      isIso_spec_residueFieldMap φ (hU.primeIdealOf ⟨f x, hxU⟩) u₀
        (PrimeSpectrum.ext (P.over_def _)) hres
    have : IsIso ((Spec.map φ ≫ hU.fromSpec).residueFieldMap u₀) := by
      rw [Scheme.residueFieldMap_comp]
      infer_instance
    have hvq : pullback.snd f _ (W₁.ι v₀) = u₀ := by
      change (g ≫ pullback.snd f _) ⟨P', ‹_›⟩ = u₀
      rw [hgq]
      exact PrimeSpectrum.ext (P'.over_def P).symm
    have : IsIso ((Spec.map φ ≫ hU.fromSpec).residueFieldMap
        (pullback.snd f _ (W₁.ι v₀))) := by
      rw [hvq]
      infer_instance
    have := isIso_pullback_fst_residueFieldMap f (Spec.map φ ≫ hU.fromSpec) (W₁.ι v₀)
    rw [Scheme.residueFieldMap_comp]
    infer_instance

end AlgebraicGeometry
