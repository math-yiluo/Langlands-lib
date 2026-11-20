import Langlands.GroupScheme.SplitSolvableSectionsStatement
import Langlands.GroupScheme.Rational.SplitSolvableExtensionStructure
import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TorusVectorLinearizationProof
import Langlands.GroupScheme.Rational.SolvableMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.GroupScheme.Unipotent.MultiplicativeTrivialityProof

/-! # Sections of the canonical extension of a split solvable group (Milne 16.54)

We prove `SplitSolvableExtensionSectionsStatement`. By
`IsSplitSolvableGroupScheme.canonicalExtension_structure`, the kernel of `q` has the same
points as a smooth connected split unipotent closed subgroup, and `D` is a split torus. The
Library's section theorem for split unipotent extensions of tori then gives a section. Every
section is a maximal split torus of `G`, so two sections are conjugate by the conjugacy of
maximal split tori in smooth connected solvable groups; the conjugating point can be moved
into the kernel because the target is commutative. Finally, a closed split torus that is
maximal for inclusion of ranges is a maximal split torus, hence conjugate to a section, and
its range is the range of the conjugated section; conversely, a closed split torus with the
range of a section is maximal because closed split tori meet the unipotent kernel trivially.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitSolvableSections

variable {k : Type u} [Field k] {G U D : GroupScheme (Spec (CommRingCat.of k))}

/-- A closed split torus and a closed unipotent subgroup of an affine algebraic group meet
trivially on every test scheme. -/
theorem range_inf_eq_bot [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    {S : GroupScheme (Spec (CommRingCat.of k))} (j : S ⟶ G) (hj : IsClosedSubgroup j)
    (hS : IsSplitTorus S) (i : U ⟶ G) (hi : IsClosedSubgroup i) (hU : IsUnipotent U) :
    SubgroupFunctor.range j ⊓ SubgroupFunctor.range i = ⊥ := by
  have h := (unipotentMultiplicativeTriviality k).2.1 G U S i j hi hj hU
    hS.isTorus.isMultiplicativeType
  ext T x
  have hx := congrArg (fun F : SubgroupFunctor G => x ∈ F.carrier T) h
  simp only [SubgroupFunctor.inf_carrier, Subgroup.mem_inf] at hx ⊢
  rw [and_comm]
  exact Iff.of_eq hx

/-- A homomorphic section of the quotient of `G` by a closed unipotent subgroup onto a split
torus is a maximal split torus of `G`. -/
theorem isMaximalSplitTorus_of_comp_eq_id [LocallyOfFiniteType G.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : U ⟶ G} {q : G ⟶ T.toGrp}
    (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i)
    (hD : IsSplitTorus T.toGrp) (s : T.toGrp ⟶ G) (hs : s ≫ q = 𝟙 T.toGrp) :
    IsMaximalSplitTorus s := by
  refine ⟨⟨hD, IsClosedSubgroup.of_comp_eq_id s q hs⟩, ?_⟩
  intro T' i' hi' f hf
  have hint := range_inf_eq_bot i' hi'.2 hi'.1 i hi hU
  have : Mono i'.hom.hom.left := hi'.2.mono
  have hmono : Mono (i' ≫ q).hom.hom :=
    mono_comp_of_inf_eq_bot (Over.mono_of_mono_left _) hq hint
  have : Mono (i' ≫ q) := (Grp.forget _).mono_of_mono_map hmono
  have hfq : f ≫ i' ≫ q = 𝟙 _ := by
    rw [← Category.assoc, hf]
    exact hs
  have : IsSplitEpi (i' ≫ q) := IsSplitEpi.mk' ⟨f, hfq⟩
  have : IsIso (i' ≫ q) := isIso_of_mono_of_isSplitEpi _
  have hfinv : f = inv (i' ≫ q) := by
    rw [← cancel_mono (i' ≫ q), hfq, IsIso.inv_hom_id]
  rw [hfinv]
  infer_instance

/-- Conjugating a section of a homomorphism onto a split torus by a rational point `g` agrees
with conjugating it by a rational point of the kernel. -/
theorem exists_kernel_point_conj {i : U ⟶ G} {q : G ⟶ D}
    (hq : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i) (hD : IsSplitTorus D)
    (s : D ⟶ G) (hs : s ≫ q = 𝟙 D) (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
      s ≫ (G.innerIso g).hom = s ≫ (G.innerIso (v ≫ i.hom.hom)).hom := by
  set d := g ≫ q.hom.hom with hd
  set h := d ≫ s.hom.hom with hh
  have hhq : h ≫ q.hom.hom = d := by
    rw [hh, Category.assoc, ← Grp.comp_hom_hom, hs]
    rfl
  have hw : g * h⁻¹ ∈ (SubgroupFunctor.range (kernelι q)).carrier _ := by
    rw [mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, hhq, ← hd, mul_inv_cancel]
  rw [hq] at hw
  obtain ⟨v, hv⟩ := SubgroupFunctor.mem_range.mp hw
  refine ⟨v, ?_⟩
  have hg : g = (v ≫ i.hom.hom) * h := by
    rw [hv, inv_mul_cancel_right]
  have hsh : s ≫ (G.innerIso h).hom = s := by
    rw [hh, ← innerIso_hom_comp, hD.innerIso_hom, Category.id_comp]
  rw [hg, innerIso_mul_hom, ← Category.assoc, hsh]

end SplitSolvableSections

open SplitSolvableSections in
/-- Milne 2017, Proposition 16.54. -/
theorem splitSolvableExtensionSections : SplitSolvableExtensionSectionsStatement.{u} := by
  intro k _ G hG U D i q hi hU _hn hq hD
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨U', i', hi', hU's, hU'c, hU'u, hU'split, hrange, hDsplit⟩ :=
    hG.canonicalExtension_structure i q hi hU hq hD
  have hker : SubgroupFunctor.range (kernelι q) = SubgroupFunctor.range i := hq.2.2.2
  -- Regard the split torus `D` as a commutative group scheme.
  obtain ⟨T, rfl⟩ : ∃ T : CommGroupScheme (Spec (CommRingCat.of k)), T.toGrp = D :=
    ⟨hDsplit.toCommGroupScheme, rfl⟩
  -- (a) Existence of a section.
  have hsec : ∃ s : T.toGrp ⟶ G, s ≫ q = 𝟙 T.toGrp := by
    have : Smooth U'.X.hom := hU's
    have : ConnectedSpace U'.X.left := hU'c
    have : Mono i'.hom.hom.left := hi'.mono
    have : Mono i'.hom.hom := Over.mono_of_mono_left _
    have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i') q := by
      rw [hrange]
      exact hq
    exact IsTorus.exists_splitUnipotentExtensionSection (E := G) i' q hq' hU'u hU'split
      RelativeRoot.splitUnipotentStableVectorSubgroup RelativeRoot.torusVectorActionLinearization
      hDsplit.isTorus
  -- Every section is a maximal split torus.
  have hmaxsec : ∀ s : T.toGrp ⟶ G, s ≫ q = 𝟙 T.toGrp → IsMaximalSplitTorus s :=
    fun s hs => isMaximalSplitTorus_of_comp_eq_id hi hU hker hDsplit s hs
  refine ⟨hsec, ?_, ?_⟩
  -- (b) Any two sections are conjugate by a rational point of the kernel.
  · intro s₁ s₂ hs₁ hs₂
    obtain ⟨g, e, hge⟩ := solvableMaximalSplitTorusConjugacy k G hG.isSolvableGroupScheme
      T T s₁ s₂ (hmaxsec s₁ hs₁) (hmaxsec s₂ hs₂)
    have he : e.hom = 𝟙 T.toGrp := by
      have h := congrArg (· ≫ q) hge
      simp only [Category.assoc, innerIso_hom_comp_of_isSplitTorus hDsplit q g] at h
      rw [hs₁, hs₂, Category.comp_id] at h
      exact h.symm
    have h₂ : s₂ = s₁ ≫ (G.innerIso g).hom := by
      rw [hge, he, Category.id_comp]
    obtain ⟨v, hv⟩ := exists_kernel_point_conj hker hDsplit s₁ hs₁ g
    exact ⟨v, h₂.trans hv⟩
  -- (c) Maximal closed split tori are exactly the ranges of sections.
  · intro S j hj hS
    obtain ⟨TS, rfl⟩ : ∃ TS : CommGroupScheme (Spec (CommRingCat.of k)), TS.toGrp = S :=
      ⟨hS.toCommGroupScheme, rfl⟩
    constructor
    · intro hmax
      have hjmax : IsMaximalSplitTorus j := by
        refine ⟨⟨hS, hj⟩, ?_⟩
        intro T' j' hj' f hf
        have hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range j' := by
          rw [SubgroupFunctor.le_def]
          intro V x hx
          obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
          refine SubgroupFunctor.mem_range.mpr ⟨y ≫ f.hom.hom, ?_⟩
          rw [Category.assoc, ← Grp.comp_hom_hom, hf]
        have heq := hmax T'.toGrp j' hj'.2 hj'.1 hle
        have : Mono j.hom.hom.left := hj.mono
        have : Mono j'.hom.hom.left := hj'.2.mono
        have hjrep : (SubgroupFunctor.range j').IsRepresentedBy j :=
          ⟨Over.mono_of_mono_left _, heq⟩
        have hj'rep : (SubgroupFunctor.range j').IsRepresentedBy j' :=
          ⟨Over.mono_of_mono_left _, rfl⟩
        have : Mono j' := (Grp.forget _).mono_of_mono_map hj'rep.1
        have hfe : f = (hjrep.isoOfIsRepresentedBy hj'rep).hom := by
          rw [← cancel_mono j', hf, SubgroupFunctor.IsRepresentedBy.isoOfIsRepresentedBy_hom_comp]
        rw [hfe]
        infer_instance
      obtain ⟨s₀, hs₀⟩ := hsec
      obtain ⟨g, e, hge⟩ := solvableMaximalSplitTorusConjugacy k G hG.isSolvableGroupScheme
        TS T j s₀ hjmax (hmaxsec s₀ hs₀)
      refine ⟨s₀ ≫ (G.innerIso g).inv, ?_, ?_⟩
      · have hinv : (G.innerIso g).inv ≫ q = q := by
          rw [Iso.inv_comp_eq, innerIso_hom_comp_of_isSplitTorus hDsplit q g]
        rw [Category.assoc, hinv, hs₀]
      · have hj' : j = e.hom ≫ s₀ ≫ (G.innerIso g).inv := by
          rw [← Category.assoc, Iso.eq_comp_inv, hge]
        rw [hj', SubgroupFunctor.range_iso_comp]
    · rintro ⟨s, hs, hjs⟩ S' j' hj' hS' hle
      refine le_antisymm hle ?_
      rw [SubgroupFunctor.le_def]
      intro V x hx
      set y := x ≫ q.hom.hom ≫ s.hom.hom with hy
      have hys : y ∈ (SubgroupFunctor.range s).carrier V :=
        SubgroupFunctor.mem_range.mpr ⟨x ≫ q.hom.hom, rfl⟩
      have hyj' : y ∈ (SubgroupFunctor.range j').carrier V := by
        rw [← hjs] at hys
        exact SubgroupFunctor.le_def.mp hle V hys
      have hyq : y ≫ q.hom.hom = x ≫ q.hom.hom := by
        rw [hy, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, hs]
        rfl
      have hz : x * y⁻¹ ∈ (SubgroupFunctor.range j' ⊓ SubgroupFunctor.range i).carrier V := by
        rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf]
        refine ⟨Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hyj'), ?_⟩
        rw [← hker, mem_range_kernelι_iff, MonObj.mul_comp, GrpObj.inv_comp, hyq,
          mul_inv_cancel]
      rw [range_inf_eq_bot j' hj' hS' i hi hU, SubgroupFunctor.bot_carrier, Subgroup.mem_bot,
        mul_inv_eq_one] at hz
      rw [hjs, hz]
      exact hys

end Langlands.GroupScheme
