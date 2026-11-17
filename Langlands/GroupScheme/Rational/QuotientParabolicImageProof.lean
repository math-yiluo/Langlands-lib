import Langlands.GroupScheme.Rational.QuotientParabolicImageStatement
import Langlands.GroupScheme.Absolute.GeometricBorelDescent
import Langlands.GroupScheme.Absolute.BruhatCoveringSteps
import Langlands.GroupScheme.Absolute.ProperSolvableQuotientProof
import Langlands.GroupScheme.Absolute.FiniteIndexQuotientProperProof
import Langlands.GroupScheme.Absolute.QuotientNormalizer
import Langlands.GroupScheme.Absolute.RationalPointClosureSolvable
import Langlands.GroupScheme.ParabolicQuotientProperProof
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.SubgroupBaseChange

/-! # Proof: quotient maps carry parabolic and Borel subgroups to parabolic and Borel subgroups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace QuotientParabolicImage

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Over an algebraically closed field, let `q : G ⟶ Q` be surjective, with `G` and `Q`
smooth, affine and connected. If `i : B ⟶ G` is Borel and `j : I ⟶ Q` is a smooth closed
subgroup receiving a surjective `f : B ⟶ I` with `i ≫ q = f ≫ j`, then `j` is Borel. -/
theorem isBorelSubgroup_image
    {G Q B I : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q) [Surjective q.hom.hom.left]
    (i : B ⟶ G) (hi : IsBorelSubgroup i) (j : I ⟶ Q) (f : B ⟶ I)
    (hj : IsClosedSubgroup j) [Smooth I.X.hom] [Surjective f.hom.hom.left]
    (hcomm : i ≫ q = f ≫ j) : IsBorelSubgroup j := by
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  -- The image `I` is connected.
  have hIc : ConnectedSpace I.X.left :=
    Function.Surjective.connectedSpace (Surjective.surj (f := f.hom.hom.left))
      f.hom.hom.left.continuous
  -- The image `I` is solvable.
  have : LocallyOfFiniteType f.hom.hom.left := by
    have : LocallyOfFiniteType (f.hom.hom.left ≫ I.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact locallyOfFiniteType_of_comp f.hom.hom.left I.X.hom
  have : Group.IsSolvable (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) :=
    (isSolvableGroupScheme_iff_isSolvable_points B).mp hi.isSolvableGroupScheme
  let fPoints : (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ B.X) →*
      (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ I.X) :=
    ((yonedaGrp.map f).app (op (Over.mk (𝟙 (Spec (CommRingCat.of k)))))).hom
  have hIv : IsSolvableGroupScheme I :=
    (isSolvableGroupScheme_iff_isSolvable_points I).mpr
      (Group.isSolvable_of_surjective (f := fPoints) (rationalPoints_surjective f))
  -- A homogeneous quotient `G/B`; it is proper.
  obtain ⟨X, p, hXs, hXl, hXq, hps, hpsurj, hpq, hpfib⟩ :=
    smoothSubgroupQuotientExistence k G B i hi.isClosedSubgroup hi.smooth
  have hXp : IsProper X.hom :=
    parabolicSubgroupQuotientProper k G inferInstance B i
      (BruhatCovering.isParabolicSubgroup_of_isBorelSubgroup hi) X p hXs hXl hXq hps hpsurj
      hpq hpfib
  -- A homogeneous quotient `Q/I`.
  obtain ⟨R, r, hRs, hRl, hRq, hrs, hrsurj, hrq, hrfib⟩ :=
    smoothSubgroupQuotientExistence k Q I j hj inferInstance
  have : Smooth p.left := hps
  have : Surjective p.left := hpsurj
  have : QuasiCompact p.left := hpq
  have : Surjective r.left := hrsurj
  -- The composite `G ⟶ Q ⟶ Q/I` is constant on the cosets of `B`.
  have hq' : i.hom.hom ≫ q.hom.hom = f.hom.hom ≫ j.hom.hom :=
    congrArg (fun φ : B ⟶ Q => φ.hom.hom) hcomm
  obtain ⟨ρ, hρ⟩ := FiniteIndexTransfer.exists_factor i (q.hom.hom ≫ r) p
    (fun T g h e => (hpfib T g h).mp e) (by
      intro T g h hgh
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hgh
      have hmem : (g ≫ q.hom.hom)⁻¹ * (h ≫ q.hom.hom) ∈
          (SubgroupFunctor.range j).carrier T := by
        refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
        rw [Category.assoc, ← hq', ← Category.assoc, hy, MonObj.mul_comp, GrpObj.inv_comp]
      have h' := (hrfib T _ _).mpr hmem
      simpa only [Category.assoc] using h')
  have hρl : p.left ≫ ρ.left = q.hom.hom.left ≫ r.left :=
    congrArg CommaMorphism.left hρ
  -- The descended map `G/B ⟶ Q/I` is surjective, so `Q/I` is proper.
  have : Surjective (p.left ≫ ρ.left) := by
    rw [hρl]
    infer_instance
  have : Surjective ρ.left := Surjective.of_comp p.left ρ.left
  have : UniversallyClosed (ρ.left ≫ R.hom) := by
    rw [Over.w ρ]
    infer_instance
  have : UniversallyClosed R.hom := UniversallyClosed.of_comp_surjective ρ.left R.hom
  have : IsSeparated R.hom := hRs
  have : LocallyOfFiniteType R.hom := hRl
  have hRp : IsProper R.hom := ⟨⟩
  exact properSolvableQuotientBorel k Q inferInstance I j hj inferInstance hIc hIv R r hRp
    hrs hrsurj hrq hrfib

end AlgClosed

end QuotientParabolicImage

open QuotientParabolicImage in
/-- Milne, 17.69: quotient maps of smooth connected affine groups over an arbitrary field carry
parabolic subgroups to parabolic subgroups and geometric Borel subgroups to geometric Borel
subgroups. -/
theorem quotientParabolicImage : QuotientParabolicImageStatement.{u} := by
  intro k _ G Q _ _ _ _ _ _ q _ hqs H H' i j f hj hH' hf hcomm
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have : Smooth (F.obj G).X.hom := by
    change Smooth (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj G).X.left := G.connectedSpace_baseChange_of_smooth_affine b
  have : Smooth (F.obj Q).X.hom := by
    change Smooth (pullback.snd Q.X.hom b)
    infer_instance
  have : IsAffineHom (F.obj Q).X.hom := by
    change IsAffineHom (pullback.snd Q.X.hom b)
    infer_instance
  have : ConnectedSpace (F.obj Q).X.left := Q.connectedSpace_baseChange_of_smooth_affine b
  have : Surjective (F.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Surjective) b q.hom.hom hqs
  have : Smooth H'.X.hom := hH'
  have : Smooth (F.obj H').X.hom := by
    change Smooth (pullback.snd H'.X.hom b)
    infer_instance
  have hjK : IsClosedSubgroup (F.map j) := hj.baseChange b
  refine ⟨fun hP => ?_, fun hB => ?_⟩
  · obtain ⟨B₀, b₀, g₀, hb₀, hg₀⟩ := hP.exists_isBorelSubgroup
    have : Smooth B₀.X.hom := hb₀.smooth
    have : ConnectedSpace B₀.X.left := hb₀.connectedSpace
    have : IsClosedImmersion b₀.hom.hom.left := hb₀.isClosedSubgroup
    have : IsAffineHom B₀.X.hom := by
      rw [← Over.w b₀.hom.hom]
      infer_instance
    have : IsClosedImmersion (F.map j).hom.hom.left := hjK
    have : IsAffineHom (F.obj H').X.hom := by
      rw [← Over.w (F.map j).hom.hom]
      infer_instance
    obtain ⟨I, inc, fac, hinc, hfac, _, hfacs, _, _, hIs, _, _⟩ :=
      HomImage.exists_image (g₀ ≫ F.map f)
    have : Smooth I.X.hom := hIs
    have : Surjective fac.hom.hom.left := hfacs
    have hcommK : b₀ ≫ F.map q = fac ≫ (inc ≫ F.map j) := by
      rw [← hg₀, ← Category.assoc fac, hfac, Category.assoc, Category.assoc, ← F.map_comp,
        ← F.map_comp, hcomm]
    have hB₁ : IsBorelSubgroup (inc ≫ F.map j) :=
      isBorelSubgroup_image (F.map q) b₀ hb₀ (inc ≫ F.map j) fac (hinc.comp hjK) hcommK
    exact ⟨hj, hH', I, inc ≫ F.map j, inc, hB₁, rfl⟩
  · have : Surjective f.hom.hom.left := hf
    have : Surjective (F.map f).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @Surjective) b f.hom.hom hf
    have hcommK : F.map i ≫ F.map q = F.map f ≫ F.map j := by
      rw [← F.map_comp, ← F.map_comp, hcomm]
    have hjB : IsBorelSubgroup (F.map j) :=
      isBorelSubgroup_image (F.map q) (F.map i) hB.2 (F.map j) (F.map f) hjK hcommK
    exact isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure hjB hj

end Langlands.GroupScheme
