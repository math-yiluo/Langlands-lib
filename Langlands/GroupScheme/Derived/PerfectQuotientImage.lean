import Langlands.GroupScheme.Derived.ConnectedSmoothness
import Langlands.GroupScheme.Derived.ConnectednessProof
import Langlands.GroupScheme.HomImage
import Langlands.GroupScheme.CentralIsogeny.CommutatorDescent

/-! # The derived subgroup maps onto every perfect fpqc quotient -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PerfectQuotientImage

/-- A morphism whose composite with an effective epimorphism factors through a monomorphism
itself factors through that monomorphism. -/
theorem exists_lift_of_effectiveEpi {C : Type*} [Category C] {A B X Y : C}
    (e : A ⟶ B) [EffectiveEpi e] (m : X ⟶ Y) [Mono m] (f : B ⟶ Y) (g : A ⟶ X)
    (h : g ≫ m = e ≫ f) : ∃ l : B ⟶ X, l ≫ m = f := by
  have sq : CommSq g e m f := ⟨h⟩
  exact ⟨sq.lift, sq.fac_right⟩

variable {S : Scheme.{u}}

/-- If the range of `d` contains all commutators, the commutator morphism of `G` factors
through `d`. -/
theorem exists_commutator_factor {D G : GroupScheme S} (d : D ⟶ G)
    (hd : (SubgroupFunctor.range d).ContainsCommutators) :
    ∃ w : G.X ⊗ G.X ⟶ D.X, w ≫ d.hom.hom = commutatorMap (𝟙 G) (𝟙 G) := by
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp
    (hd (G.X ⊗ G.X) (fst G.X G.X) (snd G.X G.X))
  refine ⟨w, ?_⟩
  rw [hw, ← Category.id_comp (commutatorMap (𝟙 G) (𝟙 G)), commutatorMap_points]
  simp only [Category.id_comp, Grp.id_hom_hom, Category.comp_id]

/-- Let `q : G ⟶ Q` be a quasi-compact, flat and surjective homomorphism, let `d : D ⟶ G`
have a range containing all commutators, and let `inc : C ⟶ Q` be a closed subgroup through
which `d ≫ q` factors. Then the range of `inc` contains all commutators of `Q`. -/
theorem containsCommutators_range_of_factor {C D G Q : GroupScheme S} (d : D ⟶ G)
    (q : G ⟶ Q) (inc : C ⟶ Q) (fac : D ⟶ C)
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hd : (SubgroupFunctor.range d).ContainsCommutators) (hinc : IsClosedSubgroup inc)
    (hfac : fac ≫ inc = d ≫ q) :
    (SubgroupFunctor.range inc).ContainsCommutators := by
  have : IsClosedImmersion inc.hom.hom.left := hinc
  have := CommutatorDescent.effectiveEpi_tensorHom q
  obtain ⟨w, hw⟩ := exists_commutator_factor d hd
  have hsq : (w ≫ fac.hom.hom).left ≫ inc.hom.hom.left =
      (q.hom.hom ⊗ₘ q.hom.hom).left ≫ (commutatorMap (𝟙 Q) (𝟙 Q)).left := by
    rw [← Over.comp_left, ← Over.comp_left, CommutatorDescent.tensorHom_commutatorMap,
      ← hw, Category.assoc, Category.assoc, ← Grp.comp_hom_hom, ← Grp.comp_hom_hom, hfac]
  obtain ⟨l, hl⟩ := exists_lift_of_effectiveEpi _ _ _ _ hsq
  have hlw : l ≫ C.X.hom = (Q.X ⊗ Q.X).hom := by
    rw [← Over.w inc.hom.hom, ← Category.assoc, hl, Over.w]
  let lO : Q.X ⊗ Q.X ⟶ C.X := Over.homMk l hlw
  have hlO : lO ≫ inc.hom.hom = commutatorMap (𝟙 Q) (𝟙 Q) :=
    Over.OverMorphism.ext hl
  intro T x y
  refine SubgroupFunctor.mem_range.mpr ⟨lift x y ≫ lO, ?_⟩
  rw [Category.assoc, hlO, commutatorMap_lift]
  simp only [Grp.id_hom_hom, Category.comp_id]

/-- A closed subgroup whose range is everything has a surjective underlying morphism. -/
theorem surjective_of_top_le_range {C Q : GroupScheme S} (inc : C ⟶ Q)
    (h : ⊤ ≤ SubgroupFunctor.range inc) : Surjective inc.hom.hom.left := by
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp
    (h Q.X (Subgroup.mem_top (𝟙 Q.X) : 𝟙 Q.X ∈ (⊤ : SubgroupFunctor Q).carrier Q.X))
  have hs' : s.left ≫ inc.hom.hom.left = 𝟙 Q.X.left := by
    rw [← Over.comp_left, hs, Over.id_left]
  refine ⟨fun y => ⟨s.left y, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, hs']
  rfl

end PerfectQuotientImage

open PerfectQuotientImage

variable {k : Type u} [Field k]

/-- Over a field, let `d : D ⟶ G` be a homomorphism from a smooth connected affine group whose
range contains all commutators, and let `q : G ⟶ Q` be a quasi-compact, flat and surjective
homomorphism onto an affine group of finite type whose derived subgroup is everything. Then
`d ≫ q` is surjective on underlying points. -/
theorem surjective_comp_of_containsCommutators
    {D G Q : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (q : G ⟶ Q)
    [Smooth D.X.hom] [ConnectedSpace D.X.left] [IsAffineHom D.X.hom]
    [LocallyOfFiniteType Q.X.hom] [IsAffineHom Q.X.hom]
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hd : (SubgroupFunctor.range d).ContainsCommutators)
    (hQ : derivedSubgroup Q = ⊤) : Surjective (d ≫ q).hom.hom.left := by
  obtain ⟨C, inc, fac, hinc, hfac, -, hsurj, -⟩ := HomImage.exists_image (d ≫ q)
  have hcomm := containsCommutators_range_of_factor d q inc fac hd hinc hfac
  have htop : ⊤ ≤ SubgroupFunctor.range inc := by
    rw [← hQ]
    exact derivedSubgroup_le_range inc hinc hcomm
  have := surjective_of_top_le_range inc htop
  rw [← hfac, Grp.comp_hom_hom, Over.comp_left]
  infer_instance

set_option linter.defProp false in
set_option warn.classDefReducibility false in
/-- Over a field, the derived subgroup of a smooth connected affine group maps onto every
quasi-compact, flat and surjective quotient homomorphism onto an affine group of finite type
whose derived subgroup is everything. -/
def IsDerivedSubgroup.surjective_comp_of_derivedSubgroup_eq_top
    {D G Q : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G} (hd : IsDerivedSubgroup d)
    (q : G ⟶ Q) [Smooth G.X.hom] [ConnectedSpace G.X.left] [IsAffineHom G.X.hom]
    [LocallyOfFiniteType Q.X.hom] [IsAffineHom Q.X.hom]
    [QuasiCompact q.hom.hom.left] [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    (hQ : derivedSubgroup Q = ⊤) : Surjective (d ≫ q).hom.hom.left := by
  have : Smooth D.X.hom := hd.smooth_of_connected inferInstance inferInstance inferInstance
  have : ConnectedSpace D.X.left := derivedSubgroupConnectedness k G D d hd inferInstance
  have : IsClosedImmersion d.hom.hom.left := hd.1
  have : IsAffineHom D.X.hom := by
    rw [← Over.w d.hom.hom]
    infer_instance
  exact surjective_comp_of_containsCommutators d q hd.containsCommutators hQ

end Langlands.GroupScheme
