import Langlands.GroupScheme.Rational.TorusSplitPart
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup

/-! # Ambient transfer for largest split subtori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Centralizers

variable {S : Scheme.{u}} {G : GroupScheme S}
  {A B : CommGroupScheme S}

/-- Centralizing a commutative group implies centralizing every homomorphism into it,
on every test scheme and every refinement. -/
theorem torusCentralizer_le_of_factor
    (a : A.toGrp ⟶ G) (b : B.toGrp ⟶ G)
    (f : B.toGrp ⟶ A.toGrp) (hf : f ≫ a = b) :
    torusCentralizer a ≤ torusCentralizer b := by
  intro U g hg V q x
  rw [← hf, Grp.comp_hom_hom, ← Category.assoc]
  exact hg V q (x ≫ f.hom.hom)

/-- Isomorphic embeddings of commutative group schemes have the same whole-group
centralizer on all test schemes. -/
theorem torusCentralizer_eq_of_iso
    (a : A.toGrp ⟶ G) (b : B.toGrp ⟶ G)
    (e : A.toGrp ≅ B.toGrp) (he : e.hom ≫ b = a) :
    torusCentralizer a = torusCentralizer b := by
  apply le_antisymm
  · exact torusCentralizer_le_of_factor a b e.inv (by
      rw [← he, Iso.inv_hom_id_assoc])
  · exact torusCentralizer_le_of_factor b a e.hom he

end Centralizers

section Field

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {T A B : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A split subtorus containing an ambient maximal split torus is itself ambient
maximal. Both containments use actual homomorphisms. -/
theorem IsMaximalSplitTorus.of_factor
    {b : B.toGrp ⟶ G} (hb : IsMaximalSplitTorus b)
    {a : A.toGrp ⟶ G} (ha : IsSplitSubtorus a)
    (f : B.toGrp ⟶ A.toGrp) (hf : f ≫ a = b) :
    IsMaximalSplitTorus a := by
  have : IsIso f := hb.2 A a ha f hf
  refine ⟨ha, ?_⟩
  intro C c hc g hg
  have : IsIso (f ≫ g) := hb.2 C c hc (f ≫ g) (by
    rw [Category.assoc, hg, hf])
  exact (isIso_comp_left_iff f g).mp inferInstance

/-- If a largest split subtorus of a commutative subgroup contains an ambient
maximal split torus, its ambient embedding is maximal split and has the same
whole-torus centralizer. -/
theorem IsLargestSplitSubtorus.ambient_transfer
    {a : A.toGrp ⟶ T.toGrp} (ha : IsLargestSplitSubtorus a)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (b : B.toGrp ⟶ T.toGrp) (hb : IsMaximalSplitTorus (b ≫ t)) :
    IsMaximalSplitTorus (a ≫ t) ∧
      torusCentralizer (a ≫ t) = torusCentralizer (b ≫ t) := by
  obtain ⟨f, hf, _⟩ := ha.2 B b hb.1.1
  have hfac : f ≫ (a ≫ t) = b ≫ t := by
    rw [← Category.assoc, hf]
  have hsub : IsSplitSubtorus (a ≫ t) := ha.1.comp ht
  have : IsIso f := hb.2 A (a ≫ t) hsub f hfac
  exact ⟨hb.of_factor hsub f hfac,
    (torusCentralizer_eq_of_iso (b ≫ t) (a ≫ t) (asIso f) hfac).symm⟩

/-- The transfer applies to every maximal split subtorus of an affine commutative
group locally of finite type, using its largest-split universal property. -/
theorem IsMaximalSplitTorus.ambient_transfer
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom]
    {a : A.toGrp ⟶ T.toGrp} (ha : IsMaximalSplitTorus a)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (b : B.toGrp ⟶ T.toGrp) (hb : IsMaximalSplitTorus (b ≫ t)) :
    IsMaximalSplitTorus (a ≫ t) ∧
      torusCentralizer (a ≫ t) = torusCentralizer (b ≫ t) :=
  ha.isLargestSplitSubtorus.ambient_transfer t ht b hb

/-- A closed commutative subgroup of an affine group locally of finite type
inherits the ambient maximality and centralizer containment of any ambient
maximal split torus contained in it. -/
theorem IsMaximalSplitTorus.ambient_transfer_of_isClosedSubgroup
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    {a : A.toGrp ⟶ T.toGrp} (ha : IsMaximalSplitTorus a)
    (t : T.toGrp ⟶ G) (ht : IsClosedSubgroup t)
    (b : B.toGrp ⟶ T.toGrp) (hb : IsMaximalSplitTorus (b ≫ t))
    {F : SubgroupFunctor G} (hF : torusCentralizer (b ≫ t) ≤ F) :
    IsMaximalSplitTorus (a ≫ t) ∧ torusCentralizer (a ≫ t) ≤ F := by
  have : IsClosedImmersion t.hom.hom.left := ht
  have : IsAffine T.X.left := isAffine_of_isAffineHom t.hom.hom.left
  have : LocallyOfFiniteType T.X.hom := by
    rw [← Over.w t.hom.hom]
    infer_instance
  obtain ⟨hmax, hcent⟩ := ha.ambient_transfer t ht b hb
  exact ⟨hmax, hcent ▸ hF⟩

end Field

/-- The ambient split-part transfer, uniformly over fields and closed commutative
subgroups of affine groups locally of finite type. The supplied ambient maximal
split torus is the geometric input; this statement does not assert its existence. -/
def TorusSplitPartTransferStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (T A B : CommGroupScheme (Spec (CommRingCat.of k)))
    (a : A.toGrp ⟶ T.toGrp), IsMaximalSplitTorus a →
    ∀ (t : T.toGrp ⟶ G), IsClosedSubgroup t →
      ∀ (b : B.toGrp ⟶ T.toGrp), IsMaximalSplitTorus (b ≫ t) →
        ∀ F : SubgroupFunctor G, torusCentralizer (b ≫ t) ≤ F →
          IsMaximalSplitTorus (a ≫ t) ∧ torusCentralizer (a ≫ t) ≤ F

/-- The proved uniform form of the ambient split-part transfer. -/
theorem torusSplitPartTransfer : TorusSplitPartTransferStatement.{u} := by
  intro k _ G _ _ T A B a ha t ht b hb F hF
  exact ha.ambient_transfer_of_isClosedSubgroup t ht b hb hF

end Langlands.GroupScheme
