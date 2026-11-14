import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.CentralIsogeny.FpqcReflection
import Langlands.AlgebraicGeometry.SchemeFlatPropertyDescent

/-! # Reflection along arbitrary surjective étale base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

section Properties

variable {S U : Scheme.{u}} (p : U ⟶ S) [Etale p] [Surjective p]

/-- Smoothness reflects under an arbitrary surjective étale base change. -/
theorem smooth_of_baseChange_of_etale (G : GroupScheme S)
    (h : Smooth ((GroupScheme.baseChange p).obj G).X.hom) : Smooth G.X.hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (f := G.X.hom) (g := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ h

/-- Relative affineness reflects under an arbitrary surjective étale base change. -/
theorem isAffineHom_of_baseChange_of_etale (G : GroupScheme S)
    (h : IsAffineHom ((GroupScheme.baseChange p).obj G).X.hom) : IsAffineHom G.X.hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsAffineHom) (Q := @Etale ⊓ @Surjective)
    (f := G.X.hom) (g := p) ⟨inferInstance, inferInstance⟩ h

/-- Closedness of an actual group inclusion reflects under surjective étale base change. -/
theorem IsClosedSubgroup.of_baseChange_of_etale {H G : GroupScheme S} {i : H ⟶ G}
    (hi : IsClosedSubgroup ((GroupScheme.baseChange p).map i)) : IsClosedSubgroup i :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsClosedImmersion) (Q := @Etale ⊓ @Surjective)
    (baseChange_map_isPullback p i) ⟨inferInstance, inferInstance⟩ hi

/-- Surjective étale base change detects whether an actual group map is invertible. -/
theorem isIso_of_baseChange_of_etale {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] : IsIso f := by
  let : IsIso ((GroupScheme.baseChange p).map f).hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget U).map
      ((GroupScheme.baseChange p).map f).hom.hom))
  have : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      (baseChange_map_isPullback p f)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget S).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    infer_instance
  have : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget S)
  let e : H ≅ G := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- The actual isomorphism recovered from invertibility after an étale cover. -/
def isoOfEtaleBaseChange {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] : H ≅ G :=
  letI := isIso_of_baseChange_of_etale p f
  asIso f

@[simp]
theorem isoOfEtaleBaseChange_hom {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] :
    (isoOfEtaleBaseChange p f).hom = f := rfl

open CategoryTheory.Functor CategoryTheory.Functor.LaxMonoidal in
/-- Commutativity reflects under an arbitrary surjective étale base change. -/
theorem isCommMonObj_of_baseChange_of_etale (G : GroupScheme S)
    (hG : IsCommMonObj ((GroupScheme.baseChange p).obj G).X) : IsCommMonObj G.X := by
  let F := Over.pullback p
  have : IsCommMonObj (F.obj G.X) := hG
  refine ⟨F.map_injective ?_⟩
  apply (cancel_epi (LaxMonoidal.μ F G.X G.X)).mp
  rw [Functor.map_comp, Functor.LaxBraided.braided_assoc,
    ← obj.μ_def, IsCommMonObj.mul_comm]

end Properties

namespace SubgroupFunctor

variable {S U : Scheme.{u}} (p : U ⟶ S) [Etale p] [Surjective p]
  {G H : GroupScheme S}

/-- Surjective étale base change reflects containment in any represented subgroup. -/
theorem le_range_of_etaleBaseChange_le {F : SubgroupFunctor G}
    (i : H ⟶ G) [Mono i.hom.hom]
    (h : F.baseChange p ≤ (range i).baseChange p) : F ≤ range i := by
  intro V x hx
  let W := (Over.pullback p).obj V
  let q : (Over.map p).obj W ⟶ V :=
    Over.homMk (pullback.fst V.hom p) pullback.condition
  have : EffectiveEpi q.left := by
    change EffectiveEpi (pullback.fst V.hom p)
    infer_instance
  apply mem_range_of_comp_mem_range i q
  let x' := (baseChangePointsEquiv p G W).symm (q ≫ x)
  have hx' : x' ∈ (F.baseChange p).carrier W := by
    rw [mem_baseChange]
    change baseChangePointsEquiv p G W
      ((baseChangePointsEquiv p G W).symm (q ≫ x)) ∈ F.carrier _
    rw [MulEquiv.apply_symm_apply]
    exact F.comp_mem q hx
  have hi := h W hx'
  rw [mem_baseChange] at hi
  simpa only [x', MulEquiv.apply_symm_apply] using hi

end SubgroupFunctor

section Borel

variable {S U : Scheme.{u}} {B G : GroupScheme S} [IsAffineHom G.X.hom]
  {i : B ⟶ G} (p : U ⟶ S) [Etale p] [Surjective p]

/-- The relative Borel property reflects under an arbitrary étale cover for a
supplied closed inclusion in an affine group. -/
theorem IsRelativeBorelSubgroup.of_baseChange_of_etale (hi : IsClosedSubgroup i)
    (h : IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map i)) :
    IsRelativeBorelSubgroup i := by
  let : IsClosedImmersion i.hom.hom.left := hi
  have hgeo : ∀ s : S, IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s) := by
    intro s
    obtain ⟨x, rfl⟩ := p.surjective s
    let a := S.fromSpecResidueField (p x)
    let c := Spec.map (p.residueFieldMap x)
    let : Algebra (S.residueField (p x) : Type u) (U.residueField x : Type u) :=
      (p.residueFieldMap x).hom.toAlgebra
    let : IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom := by
      change IsAffineHom (pullback.snd G.X.hom a)
      infer_instance
    apply IsGeometricBorelSubgroup.of_baseChange
      (k := (S.residueField (p x) : Type u)) (K := (U.residueField x : Type u))
      (hclosed := hi.baseChange a)
    change IsGeometricBorelSubgroup
      ((GroupScheme.baseChange c).map ((GroupScheme.baseChange a).map i))
    apply isGeometricBorelSubgroup_baseChange_comp a c i
    rw [show c ≫ a = U.fromSpecResidueField x ≫ p from
      p.SpecMap_residueFieldMap_fromSpecResidueField x]
    exact isGeometricBorelSubgroup_of_baseChange_comp p (U.fromSpecResidueField x) i
      (h.residueFiber x)
  exact ⟨⟨smooth_of_baseChange_of_etale p B h.isRelativeParabolicSubgroup.smooth,
    hi.isAffineHom, Over.mono_of_mono_left _,
    fun s => (hgeo s).isParabolicSubgroup⟩, hgeo⟩

/-- Record the actual downstairs presentation whose Borelness is detected by an étale cover. -/
def RelativeBorelData.ofEtaleBaseChange (hi : IsClosedSubgroup i)
    (h : IsRelativeBorelSubgroup ((GroupScheme.baseChange p).map i)) :
    RelativeBorelData G where
  obj := B
  inclusion := i
  isBorel := IsRelativeBorelSubgroup.of_baseChange_of_etale p hi h

end Borel

section Reductivity

variable {S U : Scheme.{u}} {G : GroupScheme S}

/-- Reductivity reflects under every surjective étale base change, with no
affineness or quasi-compactness assumption on the cover or the original group. -/
theorem IsReductive.of_baseChange_of_etale (p : U ⟶ S) [Etale p] [Surjective p]
    (hG : IsReductive ((GroupScheme.baseChange p).obj G)) : IsReductive G := by
  let : IsAffineHom G.X.hom :=
    isAffineHom_of_baseChange_of_etale p G hG.isAffineHom
  have hκ : ∀ s : S,
      IsConnectedReductive ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G) := by
    intro s
    obtain ⟨x, rfl⟩ := p.surjective s
    let a := S.fromSpecResidueField (p x)
    let c := Spec.map (p.residueFieldMap x)
    let : Algebra (S.residueField (p x) : Type u) (U.residueField x : Type u) :=
      (p.residueFieldMap x).hom.toAlgebra
    have h := (hG.isConnectedReductive_residueFiber x).of_iso
      (baseChangeCompIso p (U.fromSpecResidueField x) G)
    rw [← p.SpecMap_residueFieldMap_fromSpecResidueField x] at h
    exact IsConnectedReductive.of_fieldExtension
      (k := (S.residueField (p x) : Type u)) (K := (U.residueField x : Type u))
      (h.of_iso (baseChangeCompIso a c G).symm)
  refine ⟨smooth_of_baseChange_of_etale p G hG.smooth, inferInstance, fun s => ?_⟩
  have h := connectedReductiveFieldExtensionStatement
    (S.residueField s) (AlgebraicClosure (S.residueField s)) _ (hκ s)
  exact (h.of_iso
    (baseChangeCompIso (S.fromSpecResidueField s) (toAlgebraicClosure _) G)).isPseudoReductive

end Reductivity

end Langlands.GroupScheme
