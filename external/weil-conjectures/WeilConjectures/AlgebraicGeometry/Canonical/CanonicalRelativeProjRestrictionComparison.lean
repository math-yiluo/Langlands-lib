/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.AbelianVariety.CoherentFiniteType

/-! # Restriction comparison for the canonical relative Proj

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC, affine-local comparison.
(blueprint: lem-trf-canonical-relative-proj-restriction-comparison).
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

private theorem grading_eq {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (D : ℕ → Submodule R A) (g h : GradedAlgebra D) : g = h := by
  have e : g.toDecomposition = h.toDecomposition := Subsingleton.elim _ _
  cases g
  cases h
  cases e
  rfl

private theorem symmetricProj_congr {R : Type u} [CommRing R]
    (M N : ModuleCat.{u} R) (h : M = N)
    (gM : GradedAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι R M).range ^ n))
    (gN : GradedAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι R N).range ^ n)) :
    letI := gM
    letI := gN
    ∃ e : Proj (fun n : ℕ ↦ (SymmetricAlgebra.ι R M).range ^ n) ≅
      Proj (fun n : ℕ ↦ (SymmetricAlgebra.ι R N).range ^ n),
      e.hom ≫ Proj.toSpecOfAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι R N).range ^ n) =
        Proj.toSpecOfAlgebra (fun n : ℕ ↦ (SymmetricAlgebra.ι R M).range ^ n) := by
  subst N
  have hg := grading_eq _ gM gN
  subst gN
  exact ⟨Iso.refl _, Category.id_comp _⟩

private theorem module_eq {S : Scheme.{u}} (E : S.Modules) (U : S.Opens)
    (V : U.toScheme.Opens) :
    ((E.restrict U.ι).val.obj (op V)).isModule =
      (E.val.obj (op (U.ι ''ᵁ V))).isModule := by
  change Module.compHom (E.val.obj (op (U.ι ''ᵁ V)))
    (U.ι.appIso V).inv.hom = _
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  apply Module.ext
  rfl

private theorem moduleObj_eq {S : Scheme.{u}} (E : S.Modules) (U : S.Opens)
    (V : U.toScheme.Opens) :
    (E.restrict U.ι).val.obj (op V) = E.val.obj (op (U.ι ''ᵁ V)) := by
  change @ModuleCat.of Γ(S, U.ι ''ᵁ V) _ _ _
    ((E.restrict U.ι).val.obj (op V)).isModule =
      @ModuleCat.of Γ(S, U.ι ''ᵁ V) _ _ _ (E.val.obj (op (U.ι ''ᵁ V))).isModule
  rw [module_eq]
  rfl

private theorem chart_iso {S : Scheme.{u}} (E : S.Modules) [E.IsQuasicoherent]
    (U : S.Opens) [(E.restrict U.ι).IsQuasicoherent] (V : U.toScheme.affineOpens) :
    let A := SymmetricAlgebraSheaf.gradedAlgebraData E
    let B := SymmetricAlgebraSheaf.gradedAlgebraData (E.restrict U.ι)
    let W : S.affineOpens := ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩
    ∃ e : B.relProjFunctor.obj V ≅ A.relProjFunctor.obj W,
      e.hom ≫ A.toOpen W ≫ W.1.ι = B.toOpen V ≫ V.1.ι ≫ U.ι := by
  dsimp only
  obtain ⟨e, he⟩ := symmetricProj_congr (R := Γ(S, U.ι ''ᵁ V.1))
    _ _ (moduleObj_eq E U V.1)
    (SymmetricAlgebraSheaf.sectionGradedAlgebra (E.restrict U.ι) V)
    (SymmetricAlgebraSheaf.sectionGradedAlgebra E
      ⟨U.ι ''ᵁ V.1, V.2.image_of_isOpenImmersion U.ι⟩)
  have h := IsAffineOpen.SpecMap_appLE_fromSpec U.ι
    (V.2.image_of_isOpenImmersion U.ι) V.2 (U.ι.preimage_image_eq V.1).ge
  rw [← Scheme.Hom.appIso_hom', Scheme.Opens.ι_appIso, Iso.refl_hom,
    Spec.map_id] at h
  have h' := (Category.id_comp _).symm.trans h
  have hp := congrArg (fun f ↦ f ≫ (V.2.image_of_isOpenImmersion U.ι).fromSpec) he
  refine ⟨e, ?_⟩
  convert hp using 1
  · rfl
  · simp only [Scheme.GradedAlgebraData.toOpen, IsAffineOpen.fromSpec, Category.assoc]
    rfl
  · rw [h']
    simp only [Scheme.GradedAlgebraData.toOpen, IsAffineOpen.fromSpec, Category.assoc]
    rfl

/-- The canonical relative Proj commutes with restriction to an affine open: the relative Proj
of Sym(E|_U) over U is isomorphic, over U, to the preimage of U in the relative Proj of Sym(E).

Source: Stacks Project, Morphisms, Lemmas 01WB and 01WC, affine-local comparison;
Constructions, Tag 01NQ.
Proof: for an affine open V ⊆ U, the sections of E|_U over V are the sections of E over the
image of V in S, so the canonical graded algebra of Sym(E|_U) on V is the canonical graded
algebra of Sym(E) on the image of V, compatibly with the restriction maps.  Both relative
Proj schemes are glued from the charts Proj(Sym(E)(V)) along the same transition maps, and
over each such V the preimage of V in the global relative Proj is the chart Proj(Sym(E)(V))
(`isPullback_relProjι`).  Hence the chart embeddings of the relative Proj over U into the
preimage of U glue to an isomorphism; on each chart it commutes with the structure maps
(`relProjι_relProjHom`), so `e.hom ≫ (relProjHom ∣_ U)` equals the structure map over U.
(blueprint: lem-trf-canonical-relative-proj-restriction-comparison). -/
theorem exists_canonicalRelativeProj_restrict_iso {S : Scheme.{u}} (E : S.Modules)
    (hE : E.IsQuasiCoherentFiniteType) (U : S.Opens) (hU : IsAffineOpen U)
    (hq : (E.restrict U.ι).IsQuasicoherent) :
    ∃ (e : (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme (E.restrict U.ι) hq).relProj ≅
      ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ⁻¹ᵁ U).toScheme),
      e.hom ≫ ((@SymmetricAlgebraSheaf.gradedAlgebraData S E hE.1).relProjHom ∣_ U) =
        (@SymmetricAlgebraSheaf.gradedAlgebraData U.toScheme (E.restrict U.ι) hq).relProjHom := by
  have : E.IsQuasicoherent := hE.1
  have : (E.restrict U.ι).IsQuasicoherent := hq
  have : IsAffine U.toScheme := hU
  let A := SymmetricAlgebraSheaf.gradedAlgebraData E
  let B := SymmetricAlgebraSheaf.gradedAlgebraData (E.restrict U.ι)
  let T : U.toScheme.affineOpens := ⟨⊤, isAffineOpen_top U.toScheme⟩
  let V : S.affineOpens := ⟨U.ι ''ᵁ T.1, T.2.image_of_isOpenImmersion U.ι⟩
  obtain ⟨e, hej⟩ := chart_iso E U T
  have : IsIso T.1.ι := inferInstanceAs (IsIso U.toScheme.topIso.hom)
  have : IsIso (B.relProjι T) := (B.isPullback_relProjι T).isIso_snd_of_isIso
  let ec := (A.isPullback_relProjι V).isoIsPullback _ _
    (isPullback_morphismRestrict A.relProjHom V.1)
  have hVU : V.1 = U := U.ι_image_top
  let er := A.relProj.isoOfEq (congrArg (fun W ↦ A.relProjHom ⁻¹ᵁ W) hVU)
  let ei := (asIso (B.relProjι T)).symm ≪≫ e ≪≫ ec ≪≫ er
  refine ⟨ei, ?_⟩
  change ei.hom ≫ (A.relProjHom ∣_ U) = B.relProjHom
  apply (cancel_epi (B.relProjι T)).mp
  apply (cancel_mono U.ι).mp
  simp only [Category.assoc, morphismRestrict_ι]
  dsimp only [ei, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  simp only [er, ec, Category.assoc, IsIso.hom_inv_id_assoc,
    Scheme.isoOfEq_hom_ι_assoc, IsPullback.isoIsPullback_hom_snd_assoc,
    Scheme.GradedAlgebraData.relProjι_relProjHom,
    Scheme.GradedAlgebraData.relProjι_relProjHom_assoc]
  exact hej

end AlgebraicGeometry

end
