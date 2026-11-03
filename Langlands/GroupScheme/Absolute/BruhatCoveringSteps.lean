import Langlands.GroupScheme.Absolute.BruhatCoveringStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.AlgebraicClosureBaseChange
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyReduction
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerStatement
import Langlands.GroupScheme.Absolute.CentralizerBorelIntersectionStatement
import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStatement
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.HomogeneousQuotientProof
import Langlands.GroupScheme.FixedCosetFactorization
import Langlands.GroupScheme.SchemeAction
import Langlands.AbelianScheme.AlgClosedIsogenyPointLifting

/-! # Steps of the absolute Bruhat covering: cocharacter, quotient and normalizer point -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatCovering

variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G B : GroupScheme (Spec (CommRingCat.of k))}
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A Borel pair over an algebraically closed field carries a cocharacter of the torus whose
dynamic parabolic subgroup is represented by the Borel subgroup and whose dynamic centralizer
is the torus. -/
theorem exists_cocharacter
    (hsplit : TorusFiniteGaloisSplittingStatement.{u})
    (hreg : RegularCocharacterBorelStatement.{u})
    (hgen : GenericCentralizerStatement.{u})
    (hcent : MaximalTorusCentralizerStatement.{u})
    (hG : IsConnectedReductive G) {i : B ⟶ G} {j : T.toGrp ⟶ G} (hij : IsBorelPair i j) :
    ∃ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ T.toGrp,
      (Dynamic.parabolic (ν ≫ j)).IsRepresentedBy i ∧
        Dynamic.centralizer (ν ≫ j) = SubgroupFunctor.range j := by
  have := hG.isAffineHom
  obtain ⟨hi, hj, f, hf⟩ := hij
  have hT : IsSplitTorus T.toGrp := hj.1.isSplitTorus_of_finiteGaloisSplitting hsplit
  obtain ⟨ν, hν, hP⟩ := (hreg k G hG T j hT hj).2.2 B i f hi hf
  have hZ := hgen k G hG T j (hj.isMaximalSplitTorus hT) ν hν
  refine ⟨CommGroupScheme.groupHom ν, hP, ?_⟩
  rw [hZ, hcent k G hG T j hj]

/-- Over an algebraically closed field a Borel subgroup is parabolic. -/
theorem isParabolicSubgroup_of_isBorelSubgroup {i : B ⟶ G} (hi : IsBorelSubgroup i) :
    IsParabolicSubgroup i := by
  have := hi.smooth
  exact ⟨hi.isClosedSubgroup, hi.smooth, _, _, 𝟙 _,
    IsBorelSubgroup.baseChange_of_bijective _ IsAlgClosed.algebraMap_bijective_of_isIntegral hi,
    Category.id_comp _⟩

/-- A Borel subgroup of a smooth connected affine group over an algebraically closed field has
a proper actual homogeneous quotient with smooth surjective quasi-compact projection. -/
theorem exists_proper_quotient
    (hproper : ParabolicSubgroupQuotientProperStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    {i : B ⟶ G} (hi : IsBorelSubgroup i) :
    ∃ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
      IsSeparated Q.hom ∧ IsProper Q.hom ∧ Smooth q.left ∧ Surjective q.left ∧
        QuasiCompact q.left ∧
        ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier V := by
  obtain ⟨Q, q, hsep, hlft, hqc, hsm, hsurj, hqqc, hfib⟩ :=
    smoothSubgroupQuotientExistence k G B i hi.isClosedSubgroup hi.smooth
  exact ⟨Q, q, hsep, hproper k G ‹_› B i (isParabolicSubgroup_of_isBorelSubgroup hi) Q q hsep
    hlft hqc hsm hsurj hqqc hfib, hsm, hsurj, hqqc, hfib⟩

omit [IsAlgClosed k] in
/-- Conjugating a homomorphism into the conjugate of a subgroup. -/
theorem range_le_conj_of_range_conj_le {H K : GroupScheme (Spec (CommRingCat.of k))}
    (a : H ⟶ G) (b : K ⟶ G) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (h : SubgroupFunctor.range (a ≫ (G.innerIso g⁻¹).hom) ≤ SubgroupFunctor.range b) :
    SubgroupFunctor.range a ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom) := by
  intro V x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp
    (h V (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩))
  refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, hz, innerIso_inv_hom, Category.assoc,
    ← Grp.comp_hom_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]

omit [IsAlgClosed k] in
/-- Conjugation by a point of a subgroup restricts to the subgroup. -/
theorem comp_innerIso_comp {H : GroupScheme (Spec (CommRingCat.of k))} (a : H ⟶ G)
    (p : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X) :
    a ≫ (G.innerIso (p ≫ a.hom.hom)).hom = (H.innerIso p).hom ≫ a := by
  refine hom_ext_points fun V x => ?_
  rw [Grp.comp_hom_hom, Grp.comp_hom_hom, ← Category.assoc, ← Category.assoc,
    comp_innerIso_hom, comp_innerIso_hom, ← constantPoint_comp, MonObj.mul_comp,
    MonObj.mul_comp, GrpObj.inv_comp]

variable [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- A base point whose coset is fixed by a cocharacter centralizing exactly the torus of a Borel
pair can be moved inside its coset to a point normalizing the torus. -/
theorem exists_normalizerPoint_of_fixed_coset
    (hcbi : CentralizerBorelIntersectionStatement.{u})
    (hsolv : SolvableMaximalTorusConjugacyStatement.{u})
    {i : B ⟶ G} {j : T.toGrp ⟶ G} (hij : IsBorelPair i j)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hZ : Dynamic.centralizer χ = SubgroupFunctor.range j)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier V)
    (h₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hfixed : ∀ (V : Over (Spec (CommRingCat.of k)))
      (t : V ⟶ (Gm (Spec (CommRingCat.of k))).toGrp.X),
      ((t ≫ χ.hom.hom) * G.constantPoint h₀ V) ≫ q = G.constantPoint h₀ V ≫ q) :
    ∃ n ∈ normalizerPoints j, n ≫ q = h₀ ≫ q := by
  obtain ⟨hi, hj, f, hf⟩ := hij
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have hTs : Smooth T.toGrp.X.hom := hj.1.smooth
  have hTc : ConnectedSpace T.toGrp.X.left := hj.1.connectedSpace
  -- The cocharacter lies in the conjugate Borel subgroup `h₀ B h₀⁻¹`.
  have hle : SubgroupFunctor.range χ ≤ SubgroupFunctor.range (i ≫ (G.innerIso h₀).hom) :=
    range_le_conj_of_range_conj_le χ i h₀ (range_conjugate_le_of_fixed_coset χ i q hfib h₀ hfixed)
  have hjrep : (Dynamic.centralizer χ).IsRepresentedBy j := ⟨inferInstance, hZ.symm⟩
  obtain ⟨C, c, hc, hcle⟩ := hcbi k G χ T.toGrp j hj.2.1 hjrep hTs hTc B
    (i ≫ (G.innerIso h₀).hom) (hi.comp_iso (G.innerIso h₀)) hle
  -- A torus is its own Borel subgroup.
  have : IsIso c := hc.maximal T.toGrp (𝟙 _) c (IsClosedSubgroup.of_iso (Iso.refl _)) hTs hTc
    (isSolvableGroupScheme_of_isCommMonObj T.toGrp) (Category.comp_id c)
  have hjle : SubgroupFunctor.range (j ≫ (G.innerIso h₀⁻¹).hom) ≤ SubgroupFunctor.range i := by
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp
      (hcle V (SubgroupFunctor.mem_range.mpr ⟨t ≫ (inv c).hom.hom, by
        rw [Grp.comp_hom_hom, ← Category.assoc, Category.assoc t, ← Grp.comp_hom_hom,
          IsIso.inv_hom_id, Grp.id_hom_hom, Category.comp_id]⟩))
    refine SubgroupFunctor.mem_range.mpr ⟨b, ?_⟩
    rw [Grp.comp_hom_hom, ← Category.assoc] at hb
    rw [Grp.comp_hom_hom, ← Category.assoc, ← hb, innerIso_inv_hom, Category.assoc,
      ← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id]
  have : Mono (j ≫ (G.innerIso h₀⁻¹).hom).hom.hom := by
    have : IsIso (G.innerIso h₀⁻¹).hom.hom.hom :=
      (inferInstance : IsIso ((Grp.forget _).mapIso (G.innerIso h₀⁻¹)).hom)
    change Mono (j.hom.hom ≫ (G.innerIso h₀⁻¹).hom.hom.hom)
    infer_instance
  let f' := SubgroupFunctor.factorOfRangeLE hjle
  have hf' : f' ≫ i = j ≫ (G.innerIso h₀⁻¹).hom := SubgroupFunctor.factorOfRangeLE_comp hjle
  -- Both embeddings are maximal tori of the Borel subgroup.
  have hfmax : IsMaximalTorus f := IsMaximalTorus.of_comp hi.isClosedSubgroup (hf ▸ hj)
  have hf'max : IsMaximalTorus f' :=
    IsMaximalTorus.of_comp hi.isClosedSubgroup (hf' ▸ hj.comp_iso (G.innerIso h₀⁻¹))
  have : Smooth B.X.hom := hi.smooth
  have : ConnectedSpace B.X.left := hi.connectedSpace
  have : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨b, e, he⟩ := (subgroupConjugate_iff_exists_commGroupSchemeIso f f').mp
    (hsolv k B hi.isSolvableGroupScheme T T f f' hfmax hf'max)
  refine ⟨h₀ * (b ≫ i.hom.hom), ⟨e, ?_⟩, ?_⟩
  · change j ≫ (G.innerIso (h₀ * (b ≫ i.hom.hom))).hom = CommGroupScheme.groupHom e.hom ≫ j
    rw [innerIso_mul_hom]
    calc j ≫ (G.innerIso (b ≫ i.hom.hom)).hom ≫ (G.innerIso h₀).hom
        = f ≫ (B.innerIso b).hom ≫ i ≫ (G.innerIso h₀).hom := by
          rw [← hf, Category.assoc, ← Category.assoc i, comp_innerIso_comp, Category.assoc]
      _ = CommGroupScheme.groupHom e.hom ≫ f' ≫ i ≫ (G.innerIso h₀).hom := by
          rw [← Category.assoc f, he, Category.assoc]
      _ = CommGroupScheme.groupHom e.hom ≫ j := by
          rw [← Category.assoc f', hf', Category.assoc, ← innerIso_mul_hom, mul_inv_cancel,
            innerIso_one_hom, Category.comp_id]
  · refine ((hfib _ h₀ (h₀ * (b ≫ i.hom.hom))).mpr ?_).symm
    rw [inv_mul_cancel_left]
    exact SubgroupFunctor.mem_range.mpr ⟨b, rfl⟩

/-- A rational quotient point fixed by the cocharacter, for an action compatible with the
projection, is the coset of a rational point normalizing the torus. -/
theorem exists_normalizerPoint_of_isFixed
    (hcbi : CentralizerBorelIntersectionStatement.{u})
    (hsolv : SolvableMaximalTorusConjugacyStatement.{u})
    {i : B ⟶ G} {j : T.toGrp ⟶ G} (hij : IsBorelPair i j)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (hZ : Dynamic.centralizer χ = SubgroupFunctor.range j)
    {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
    [LocallyOfFiniteType q.left] [Surjective q.left]
    (hfib : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier V)
    (a : SchemeAction G Q)
    (hact : ∀ (V : Over (Spec (CommRingCat.of k))) (g h : V ⟶ G.X),
      a.act g (h ≫ q) = (g * h) ≫ q)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Q) (hy : (a.restrict χ).IsFixed y) :
    ∃ n ∈ normalizerPoints j, n ≫ q = y := by
  obtain ⟨g₀, hg₀⟩ :=
    Langlands.exists_point_lift_of_locallyOfFiniteType_surjective q.left y.left
  have hgS : g₀ ≫ G.X.hom = 𝟙 (Spec (CommRingCat.of k)) := by
    rw [← Over.w q, ← Category.assoc, hg₀]
    exact Over.w y
  let h₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := Over.homMk g₀ hgS
  have hh₀ : h₀ ≫ q = y := Over.OverMorphism.ext hg₀
  obtain ⟨n, hn, hnq⟩ := exists_normalizerPoint_of_fixed_coset hcbi hsolv hij χ hZ q hfib h₀
    (fun V t => by
      have e := hy V (Over.homMk V.hom (by simp)) t
      rw [SchemeAction.restrict_act, ← hh₀, ← Category.assoc] at e
      change a.act (t ≫ χ.hom.hom) (G.constantPoint h₀ V ≫ q) =
        G.constantPoint h₀ V ≫ q at e
      rwa [hact] at e)
  exact ⟨n, hn, hnq.trans hh₀⟩

end BruhatCovering

end Langlands.GroupScheme
