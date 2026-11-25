/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.CommonRefinement
public import WeilConjectures.Compactification.BoundaryRefinement

/-!
# The closure of the diagonal is a common dense refinement

Source: literature/blueprint/main-20261015/blueprint/sec-nagata-compactification/
sk-prop-nagata-sketch-comp-category/det-nagata-refinement-common-dense.md,
node `proposition-dense-compactifications-form-cofiltered-category--1` (blueprint:
proposition-dense-compactifications-form-cofiltered-category--1).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Compactification

private lemma infFst_preimage {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c d : Compactification f) :
    (infFst c d).hom ⁻¹ᵁ c.i.opensRange = (inf c d).i.opensRange := by
  apply SetLike.coe_injective
  exact (range_snd_of_isPullback (isPullback_infFst c d).flip).symm

private lemma infSnd_preimage {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
    (c d : Compactification f) :
    (infSnd c d).hom ⁻¹ᵁ d.i.opensRange = (inf c d).i.opensRange := by
  apply SetLike.coe_injective
  exact (range_snd_of_isPullback (isPullback_infSnd c d).flip).symm

/-- For two compactifications of a separated finite-type morphism over a qcqs scheme,
the scheme-theoretic image of the diagonal graph is a dense compactification refining both;
every finite nonempty family admits such a common dense refinement. Source: blueprint
`proposition-dense-compactifications-form-cofiltered-category--1`, with Stacks Project Tags 01W3,
01W4, 01W5, 01JY, 01QR, 01RG and 01R7 (blueprint:
proposition-dense-compactifications-form-cofiltered-category--1).

Proof (the seven DAG steps):
1. Put `P = c₁.Z ×_S c₂.Z`. Its first projection is the base change of the proper
   structure map `c₂.g`, so it is proper (Stacks 01W4). Its composite with `c₁.g` is
   proper (01W3), hence separated.
2. Over the inverse image `P_k°` of either distinguished open, the graph identifies with
   `(id_X,j_ℓ) : X → X ×_S c_ℓ.Z`. This is the base change of the diagonal of the proper
   map `c_ℓ.g`: on test schemes a triple `(a,b,c)` satisfies `j_ℓ a = c = b`, so is
   uniquely determined by `a`. The diagonal is closed and closed immersions are stable
   under base change (01QR). Thus each restricted graph is closed, and the whole graph
   is an immersion, factoring as one such closed graph followed by an open immersion.
3. Each input open is quasi-compact: its composite with the proper structure map is
   the finite-type, hence quasi-compact map `f`, and the proper structure map is
   quasi-separated. Indeed its diagonal is closed, with affine inverse images of the
   form `Spec(A/I)`, hence quasi-compact. The map `P₁° → P` is a base change of `j₁`,
   hence quasi-compact. Over an affine open `V` of `P`, its inverse image in `P₁°` is
   quasi-compact, and the inverse image under the closed graph is a closed subspace
   thereof, hence quasi-compact. Therefore the graph is a quasi-compact immersion.
4. Apply the quasi-compact immersion factorization through its scheme-theoretic image
   (01RG). It gives the quasi-compact scheme-theoretically dense open `j : X → Z` and
   the closed immersion `i : Z → P` (01R7). Since `P → S` is proper, so is `Z → S`
   (01W5). Projection gives `j ≫ q_k = j_k` and the structure-map factorization, so
   these maps form a dense compactification.
5. On `Z_k° = q_k⁻¹(j_k(X))`, the closed graph from Step 2 factors through `Z_k°` and
   is still closed: locally the factorization gives ideals `I ⊆ J` and the quotient
   surjection `A/I → A/J`. But this copy of `X` is also the restriction of the dense
   open `j`. Restricting the injection `O_Z → j_* O_X` to `Z_k°` makes its kernel,
   the ideal of the closed copy of `X`, zero. The closed immersion is therefore an
   isomorphism. Hence `q_k⁻¹(j_k(X)) = j(X)` as open subschemes, including their sheaves.
6. The projections are over `S`; Step 4 gives both open triangles, and Step 5 gives
   the boundary equalities. The input opens are quasi-compact by the argument of
   Step 3, and the new open is quasi-compact by Step 4. Thus both projections satisfy
   exactly the landed three-condition refinement definition, even for non-dense inputs.
7. Induct on the positive number of compactifications. For a singleton apply Steps 1--6
   to `(c₁,c₁)`, obtaining a dense refinement without assuming the input dense. At the
   induction step take a dense common refinement `d` of the preceding members, and
   apply Steps 1--6 to `(d,c_n)`, obtaining a dense `e`. Compose the refinements to
   each preceding member: the triangles compose and the inverse-image identity is
   `(r_k a)⁻¹(j_k(X)) = a⁻¹(j_d(X)) = j_e(X)`. Enumerate any finite nonempty index
   type to obtain the conclusion; no empty-family existence assertion is used.
-/
theorem exists_common_dense_refinement {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c₁ c₂ : Compactification f) :
    IsClosedImmersion (graph c₁ c₂).imageι ∧
      IsOpenImmersion (inf c₁ c₂).i ∧ QuasiCompact (inf c₁ c₂).i ∧
      IsSchemeTheoreticallyDominant (inf c₁ c₂).i ∧
      IsProper (inf c₁ c₂).g ∧
      (graph c₁ c₂).toImage ≫ (graph c₁ c₂).imageι = graph c₁ c₂ ∧
      (inf c₁ c₂).Z = (graph c₁ c₂).image ∧
      (inf c₁ c₂).i = (graph c₁ c₂).toImage ∧
      (inf c₁ c₂).g =
        (graph c₁ c₂).imageι ≫ pullback.fst c₁.g c₂.g ≫ c₁.g ∧
      (infFst c₁ c₂).hom =
        (graph c₁ c₂).imageι ≫ pullback.fst c₁.g c₂.g ∧
      (infSnd c₁ c₂).hom =
        (graph c₁ c₂).imageι ≫ pullback.snd c₁.g c₂.g ∧
      Compactification.boundaryRefinementProperty f
          (ObjectProperty.homMk
            (X := ⟨inf c₁ c₂, (inf c₁ c₂).quasiCompact_openImmersion inferInstance⟩)
            (Y := ⟨c₁, c₁.quasiCompact_openImmersion inferInstance⟩)
            ⟨(infFst c₁ c₂).hom, (infFst c₁ c₂).i_hom, (infFst c₁ c₂).hom_g⟩) ∧
      Compactification.boundaryRefinementProperty f
          (ObjectProperty.homMk
            (X := ⟨inf c₁ c₂, (inf c₁ c₂).quasiCompact_openImmersion inferInstance⟩)
            (Y := ⟨c₂, c₂.quasiCompact_openImmersion inferInstance⟩)
            ⟨(infSnd c₁ c₂).hom, (infSnd c₁ c₂).i_hom, (infSnd c₁ c₂).hom_g⟩) ∧
      (∀ (I : Type v) [Finite I] [Nonempty I]
        (d : I → Compactification f),
        ∃ (e : Compactification f),
          IsSchemeTheoreticallyDominant e.i ∧
          ∀ i : I, ∃ (h : e.Z ⟶ (d i).Z),
            ∃ (hj : e.i ≫ h = (d i).i),
              ∃ (hS : h ≫ (d i).g = e.g),
                Compactification.boundaryRefinementProperty f
                  (ObjectProperty.homMk
                    (X := ⟨e, e.quasiCompact_openImmersion inferInstance⟩)
                    (Y := ⟨d i, (d i).quasiCompact_openImmersion inferInstance⟩)
                    ⟨h, hj, hS⟩)) := by
  classical
  have hqc (c : Compactification f) : QuasiCompact c.i :=
    c.quasiCompact_openImmersion inferInstance
  refine ⟨inferInstance, inferInstance, hqc _,
    isSchemeTheoreticallyDominant_inf_i c₁ c₂, inferInstance,
    Scheme.Hom.toImage_imageι _, inf_Z _ _, inf_i _ _, ?_,
    infFst_hom _ _, infSnd_hom _ _, ?_, ?_, ?_⟩
  · exact Category.assoc _ _ _
  · exact infFst_preimage c₁ c₂
  · exact infSnd_preimage c₁ c₂
  · intro I _ _ d
    let := Fintype.ofFinite I
    have hfinite (t : Finset I) :
        ∃ e : Compactification f, IsSchemeTheoreticallyDominant e.i ∧
          ∀ i ∈ t, ∃ r : e.Refinement (d i),
            r.hom ⁻¹ᵁ (d i).i.opensRange = e.i.opensRange := by
      induction t using Finset.induction_on with
      | empty =>
          exact ⟨inf c₁ c₁, isSchemeTheoreticallyDominant_inf_i c₁ c₁,
            fun _ hi ↦ False.elim (Finset.notMem_empty _ hi)⟩
      | @insert i t hi ih =>
          obtain ⟨e, he, ht⟩ := ih
          refine ⟨inf e (d i), isSchemeTheoreticallyDominant_inf_i e (d i), ?_⟩
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact ⟨infSnd e (d j), infSnd_preimage e (d j)⟩
          · obtain ⟨r, hr⟩ := ht j hj
            refine ⟨(infFst e (d i)).comp r, ?_⟩
            change ((infFst e (d i)).hom ≫ r.hom) ⁻¹ᵁ _ = _
            rw [Scheme.Hom.comp_preimage, hr, infFst_preimage]
    obtain ⟨e, he, ht⟩ := hfinite Finset.univ
    refine ⟨e, he, ?_⟩
    intro i
    obtain ⟨r, hr⟩ := ht i (Finset.mem_univ i)
    exact ⟨r.hom, r.i_hom, r.hom_g, hr⟩

end AlgebraicGeometry.Compactification
