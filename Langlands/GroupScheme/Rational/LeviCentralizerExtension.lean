import Langlands.GroupScheme.Rational.LeviInclusionRigidity
import Langlands.GroupScheme.Rational.CentralLeviTorusRadical
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer

/-! # Extensions of tori whose centralizers are Levis of the same group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {L M P G : GroupScheme S}

/-- Postcomposition by a scheme monomorphism reflects all-test range inclusion. -/
theorem SubgroupFunctor.range_comp_le_iff_of_mono
    (l : L ⟶ P) (m : M ⟶ P) (j : P ⟶ G) (hj : Mono j.hom.hom) :
    range (l ≫ j) ≤ range (m ≫ j) ↔ range l ≤ range m := by
  constructor
  · intro h T x hx
    obtain ⟨y, rfl⟩ := mem_range.mp hx
    obtain ⟨z, hz⟩ := mem_range.mp
      (h T (show y ≫ (l ≫ j).hom.hom ∈ (range (l ≫ j)).carrier T from
        mem_range.mpr ⟨y, rfl⟩))
    refine mem_range.mpr ⟨z, hj.right_cancellation _ _ ?_⟩
    simpa only [Grp.comp_hom_hom, ← Category.assoc] using hz
  · exact fun h => range_comp_mono h j

end Base

section Field

variable {k : Type u} [Field k]
  {G P L M : GroupScheme (Spec (CommRingCat.of k))}
  {A B : CommGroupScheme (Spec (CommRingCat.of k))}
  {j : P ⟶ G} {l : L ⟶ P} {m : M ⟶ P}
  {a : A.toGrp ⟶ G} {b : B.toGrp ⟶ G}

namespace IsRationalLeviSubgroup

variable (hl : IsRationalLeviSubgroup l) (hm : IsRationalLeviSubgroup m)
  (hj : IsClosedSubgroup j)
  (ha : (torusCentralizer a).IsRepresentedBy (l ≫ j))
  (hb : (torusCentralizer b).IsRepresentedBy (m ≫ j))
  (f : A.toGrp ⟶ B.toGrp) (hf : f ≫ b = a)

include hl hm hj ha hb f hf

/-- If an extension of commutative subgroups has a centralizer which is a
second rational Levi of the same group, the two all-test centralizers agree. -/
theorem torusCentralizer_eq_of_extension :
    torusCentralizer a = torusCentralizer b := by
  let : IsClosedImmersion j.hom.hom.left := hj
  have hjm : Mono j.hom.hom := Over.mono_of_mono_left _
  have hle : SubgroupFunctor.range m ≤ SubgroupFunctor.range l :=
    (SubgroupFunctor.range_comp_le_iff_of_mono m l j hjm).mp
      (hb.2.le.trans ((torusCentralizer_le_of_factor b a f hf).trans ha.2.ge))
  have heq := hm.range_eq_of_le hl hle
  calc
    torusCentralizer a = SubgroupFunctor.range (l ≫ j) := ha.2.symm
    _ = SubgroupFunctor.range (m ≫ j) :=
      le_antisymm (SubgroupFunctor.range_comp_mono heq.ge j)
        (SubgroupFunctor.range_comp_mono heq.le j)
    _ = torusCentralizer b := hb.2

/-- The original Levi inclusion also represents the larger subgroup's centralizer. -/
theorem represents_torusCentralizer_of_extension :
    (torusCentralizer b).IsRepresentedBy (l ≫ j) :=
  ⟨ha.1, ha.2.trans (hl.torusCentralizer_eq_of_extension hm hj ha hb f hf)⟩

/-- The canonical actual factor of the larger commutative subgroup through the
original Levi, using the proved equality of its centralizer with that Levi. -/
def centralizerExtensionFactor : B.toGrp ⟶ L :=
  torusCentralizerFactor b (hl.represents_torusCentralizer_of_extension hm hj ha hb f hf)

theorem centralizerExtensionFactor_comp :
    hl.centralizerExtensionFactor hm hj ha hb f hf ≫ l ≫ j = b :=
  torusCentralizerFactor_comp b _

/-- The larger subgroup is central in the original Levi. -/
theorem isCentral_centralizerExtensionFactor :
    IsCentral (hl.centralizerExtensionFactor hm hj ha hb f hf) :=
  isCentral_torusCentralizerFactor b _

/-- A closed larger subgroup remains closed in the original Levi. -/
theorem isClosedSubgroup_centralizerExtensionFactor (hbc : IsClosedSubgroup b) :
    IsClosedSubgroup (hl.centralizerExtensionFactor hm hj ha hb f hf) := by
  let : IsClosedImmersion l.hom.hom.left := hl.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hj
  apply isClosedSubgroup_torusCentralizerFactor b _ _ hbc
  change IsClosedImmersion (l.hom.hom.left ≫ j.hom.hom.left)
  infer_instance

/-- A split subtorus extension becomes a central split torus of the original Levi. -/
theorem isCentralSplitTorus_centralizerExtensionFactor (hbs : IsSplitSubtorus b) :
    IsCentralSplitTorus (hl.centralizerExtensionFactor hm hj ha hb f hf) :=
  ⟨⟨hbs.1, hl.isClosedSubgroup_centralizerExtensionFactor hm hj ha hb f hf hbs.2⟩,
    hl.isCentral_centralizerExtensionFactor hm hj ha hb f hf⟩

variable {R : GroupScheme (Spec (CommRingCat.of k))} {r : R ⟶ P}
  (hR : IsSolvableRadical r) (hB : IsTorus B.toGrp) (hbc : IsClosedSubgroup b)

/-- The actual factor of the larger torus through the specified solvable radical,
when both centralizers have been realized as rational Levis of the same group. -/
def centralizerExtensionRadicalFactor : B.toGrp ⟶ R :=
  hl.centralTorusRadicalFactor (hl.centralizerExtensionFactor hm hj ha hb f hf) hR hB
    (hl.isClosedSubgroup_centralizerExtensionFactor hm hj ha hb f hf hbc)
    (hl.isCentral_centralizerExtensionFactor hm hj ha hb f hf)

/-- The constructed radical factor has exactly the original ambient composite. -/
theorem centralizerExtensionRadicalFactor_comp :
    hl.centralizerExtensionRadicalFactor hm hj ha hb f hf hR hB hbc ≫ r ≫ j = b := by
  rw [centralizerExtensionRadicalFactor, ← Category.assoc,
    centralTorusRadicalFactor_comp, Category.assoc, centralizerExtensionFactor_comp]

/-- The radical factor is a closed immersion of the original torus. -/
theorem isClosedSubgroup_centralizerExtensionRadicalFactor :
    IsClosedSubgroup
      (hl.centralizerExtensionRadicalFactor hm hj ha hb f hf hR hB hbc) :=
  hl.isClosedSubgroup_centralTorusRadicalFactor
    (hl.centralizerExtensionFactor hm hj ha hb f hf) hR hB
    (hl.isClosedSubgroup_centralizerExtensionFactor hm hj ha hb f hf hbc)
    (hl.isCentral_centralizerExtensionFactor hm hj ha hb f hf)

end IsRationalLeviSubgroup

end Field

end Langlands.GroupScheme
