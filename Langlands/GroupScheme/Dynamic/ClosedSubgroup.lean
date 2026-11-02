import Langlands.AlgebraicGeometry.Morphisms.OpenCoverLift
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Reductive.Basic

/-! # Dynamic subgroups of closed subgroups

For a closed subgroup `f : H ⟶ G` of a group scheme over `S` (the underlying morphism of schemes
is a closed immersion) and a cocharacter `χ` of `H`, the dynamic subgroup functors of `H` are
the intersections of those of `G` with `H`:
`P_H(χ) = f⁻¹ P_G(χ ≫ f)`, `U_H(χ) = f⁻¹ U_G(χ ≫ f)` and `Z_H(χ) = f⁻¹ Z_G(χ ≫ f)`;
equivalently `H ∩ P_G(χ ≫ f)` is the image of `P_H(χ)`, and likewise for `U` and `Z`.
Moreover a limit in `G` of a point of `H` is the image of a limit in `H`.

No separatedness is needed. The key input is that, for every scheme `T` over `S`, a morphism
`T ×_S 𝔸¹_S ⟶ Y` factors through a closed immersion `Y' ⟶ Y` as soon as its restriction to
`T ×_S 𝔾_{m,S}` does. Over an affine open `Spec A` of `T` this holds because
`Spec A[X, X⁻¹] ⟶ Spec A[X]` is scheme-theoretically dominant, and factorizations through a
monomorphism glue along open covers.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- A morphism `f` factors through a closed immersion `i` if `j ≫ f` does for some
scheme-theoretically dominant morphism `j`. -/
theorem exists_lift_of_isSchemeTheoreticallyDominant {W X Y Y' : Scheme.{u}} (i : Y' ⟶ Y)
    [IsClosedImmersion i] (f : X ⟶ Y) (j : W ⟶ X) [IsSchemeTheoreticallyDominant j]
    (k : W ⟶ Y') (hk : k ≫ i = j ≫ f) : ∃ f' : X ⟶ Y', f' ≫ i = f := by
  have hker : (pullback.fst f i).ker = ⊥ := by
    refine le_bot_iff.mp ((Scheme.Hom.le_ker_comp (pullback.lift j k hk.symm) _).trans ?_)
    rw [pullback.lift_fst, j.ker_eq_bot]
  have : IsIso (pullback.fst f i) := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hker
  exact ⟨inv (pullback.fst f i) ≫ pullback.snd f i, by
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]⟩

namespace AffineLine

/-- Over an affine `Spec A ⟶ S`: a morphism `e : Spec A ×_S 𝔸¹_S ⟶ Y` factors through a closed
immersion `i : Y' ⟶ Y` if its restriction to `Spec A ×_S 𝔾_{m,S}` does. -/
theorem exists_lift_of_unitInclusion_affine {A : CommRingCat.{u}} (f : Spec A ⟶ S)
    {Y Y' : Over S} (i : Y' ⟶ Y) [IsClosedImmersion i.left] (e : Over.mk f ⊗ scheme S ⟶ Y)
    (k : Over.mk f ⊗ (Gm S).X ⟶ Y') (hk : k ≫ i = Over.mk f ◁ unitInclusion S ≫ e) :
    ∃ e' : (Over.mk f ⊗ scheme S).left ⟶ Y'.left, e' ≫ i.left = e.left := by
  have : IsSchemeTheoreticallyDominant (Spec.map (polynomialToLaurent A)) :=
    isSchemeTheoreticallyDominant_specMap Polynomial.toLaurent_injective
  have h : (lift (laurentInclusion f ≫ polynomialProj f)
      ((Gm.pointsEquiv _ _).symm (laurentUnit f)) ≫ k) ≫ i =
        laurentInclusion f ≫ polynomialPoint f ≫ e := by
    rw [Category.assoc, hk, ← Category.assoc, ← laurentInclusion_polynomialPoint,
      Category.assoc]
  obtain ⟨e', he'⟩ := exists_lift_of_isSchemeTheoreticallyDominant i.left
    (polynomialPoint f ≫ e).left (Spec.map (polynomialToLaurent A)) _
    (congrArg Over.Hom.left h)
  refine ⟨(polynomialPointInv f).left ≫ e', ?_⟩
  have h' : polynomialPointInv f ≫ polynomialPoint f ≫ e = e := by
    rw [← Category.assoc, polynomialPointInv_comp_polynomialPoint, Category.id_comp]
  rw [Category.assoc, he']
  exact congrArg Over.Hom.left h'

/-- A morphism `e : T ×_S 𝔸¹_S ⟶ Y` over `S` factors through a closed immersion `i : Y' ⟶ Y`
over `S` if its restriction to `T ×_S 𝔾_{m,S}` does, for every scheme `T` over `S`. -/
theorem exists_lift_of_unitInclusion {T Y Y' : Over S} (i : Y' ⟶ Y) [IsClosedImmersion i.left]
    (e : T ⊗ scheme S ⟶ Y) (k : T ⊗ (Gm S).X ⟶ Y') (hk : k ≫ i = T ◁ unitInclusion S ≫ e) :
    ∃ e' : T ⊗ scheme S ⟶ Y', e' ≫ i = e := by
  obtain ⟨e', he'⟩ : ∃ e' : (T ⊗ scheme S).left ⟶ Y'.left, e' ≫ i.left = e.left := by
    refine Langlands.AlgebraicGeometry.exists_lift_of_openCover i.left e.left
      (T.left.affineOpenCover.openCover.pullback₁ (fst T (scheme S)).left)
      fun (j : T.left.affineOpenCover.I₀) => ?_
    let a : Over.mk (T.left.affineOpenCover.f j ≫ T.hom) ⟶ T :=
      Over.homMk (T.left.affineOpenCover.f j) rfl
    obtain ⟨g, hg⟩ := exists_lift_of_unitInclusion_affine _ i (a ▷ scheme S ≫ e)
      (a ▷ (Gm S).X ≫ k) (by rw [Category.assoc, hk, whisker_exchange_assoc])
    refine ⟨pullbackFstToWhiskerRight T (T.left.affineOpenCover.f j) ≫ g, ?_⟩
    have h : pullbackFstToWhiskerRight T (T.left.affineOpenCover.f j) ≫ (a ▷ scheme S ≫ e).left =
        pullback.fst _ (T.left.affineOpenCover.f j) ≫ e.left := by
      rw [Over.comp_left, ← Category.assoc]
      exact congrArg (· ≫ e.left) (pullbackFstToWhiskerRight_comp T _)
    exact (Category.assoc _ _ _).trans ((congrArg (pullbackFstToWhiskerRight T _ ≫ ·) hg).trans h)
  refine ⟨Over.homMk e' ?_, Over.OverMorphism.ext he'⟩
  rw [← Over.w i, ← Category.assoc, he', Over.w e]

end AffineLine

namespace SubgroupFunctor

variable {H G : GroupScheme S}

/-- The image of a subgroup functor `F` of `H` under a homomorphism `f : H ⟶ G`: on every test
scheme, the images under `f` of the points of `F`. -/
def map (f : H ⟶ G) (F : SubgroupFunctor H) : SubgroupFunctor G where
  carrier T := (F.carrier T).map ((yonedaGrp.map f).app (op T)).hom
  comp_mem a x := by
    rintro ⟨y, hy, rfl⟩
    exact ⟨a ≫ y, F.comp_mem a hy, (Category.assoc a y f.hom.hom).symm⟩

theorem mem_map {f : H ⟶ G} {F : SubgroupFunctor H} {T : Over S} {x : T ⟶ G.X} :
    x ∈ (F.map f).carrier T ↔ ∃ y ∈ F.carrier T, y ≫ f.hom.hom = x :=
  Iff.rfl

/-- The image of the whole group is the range. -/
@[simp] theorem map_top (f : H ⟶ G) : (⊤ : SubgroupFunctor H).map f = range f :=
  ext fun _ => Subgroup.ext fun _ =>
    ⟨fun ⟨y, _, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, Subgroup.mem_top _, hy⟩⟩

theorem map_le_range (f : H ⟶ G) (F : SubgroupFunctor H) : F.map f ≤ range f :=
  fun _ _ ⟨y, _, hy⟩ => ⟨y, hy⟩

theorem map_le_iff_le_comap {f : H ⟶ G} {F : SubgroupFunctor H} {F' : SubgroupFunctor G} :
    F.map f ≤ F' ↔ F ≤ F'.comap f :=
  ⟨fun h T y hy => h T ⟨y, hy, rfl⟩, fun h T _ ⟨y, hy, hx⟩ => by subst hx; exact h T hy⟩

/-- The image of the preimage of `F` is the intersection of `F` with the range. -/
theorem map_comap (f : H ⟶ G) (F : SubgroupFunctor G) : (F.comap f).map f = range f ⊓ F :=
  ext fun _ => Subgroup.ext fun _ =>
    ⟨fun ⟨y, hy, hx⟩ => by subst hx; exact ⟨⟨y, rfl⟩, hy⟩,
      fun ⟨⟨y, hx⟩, h⟩ => by subst hx; exact ⟨y, h, rfl⟩⟩

/-- For a monomorphism `f`, the preimage of the image of `F` is `F`. -/
theorem comap_map_of_mono (f : H ⟶ G) [Mono f.hom.hom] (F : SubgroupFunctor H) :
    (F.map f).comap f = F :=
  ext fun _ => Subgroup.ext fun _ =>
    ⟨fun ⟨y, hy, hx⟩ => by obtain rfl := (cancel_mono f.hom.hom).mp hx; exact hy,
      fun hx => ⟨_, hx, rfl⟩⟩

end SubgroupFunctor

namespace Dynamic

variable {H G : GroupScheme S} (χ : (Gm S).toGrp ⟶ H) (f : H ⟶ G)

/-- For a closed subgroup `f : H ⟶ G`, every extension of the orbit of the image `g ≫ f` of a
point of `H` is the image of an extension of the orbit of `g`. -/
theorem IsOrbitExtension.exists_of_isClosedSubgroup (hf : IsClosedSubgroup f) {T : Over S}
    {g : T ⟶ H.X} {e : T ⊗ AffineLine.scheme S ⟶ G.X}
    (he : IsOrbitExtension (χ ≫ f) (g ≫ f.hom.hom) e) :
    ∃ e', IsOrbitExtension χ g e' ∧ e' ≫ f.hom.hom = e := by
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  obtain ⟨e', he'⟩ := AffineLine.exists_lift_of_unitInclusion f.hom.hom e (orbit χ g) (by
    rw [← orbit_comp_hom]
    exact he.symm)
  refine ⟨e', ?_, he'⟩
  rw [IsOrbitExtension, ← cancel_mono f.hom.hom, Category.assoc, he', ← orbit_comp_hom]
  exact he

/-- For a closed subgroup `f : H ⟶ G`, a limit in `G` of the image of a point of `H` is the image
of a limit in `H`. -/
theorem HasLimit.exists_of_isClosedSubgroup (hf : IsClosedSubgroup f) {T : Over S}
    {g : T ⟶ H.X} {l : T ⟶ G.X} (hl : HasLimit (χ ≫ f) (g ≫ f.hom.hom) l) :
    ∃ l', HasLimit χ g l' ∧ l' ≫ f.hom.hom = l := by
  obtain ⟨e, he, rfl⟩ := hl
  obtain ⟨e', he', rfl⟩ := he.exists_of_isClosedSubgroup χ f hf
  exact ⟨evalZero e', ⟨e', he', rfl⟩, (evalZero_comp e' _).symm⟩

/-- For a closed subgroup `f : H ⟶ G`, a point of `H` has limit `l` in `H` exactly when its
image has limit `l ≫ f` in `G`. -/
theorem hasLimit_comp_hom_iff (hf : IsClosedSubgroup f) {T : Over S} {g l : T ⟶ H.X} :
    HasLimit (χ ≫ f) (g ≫ f.hom.hom) (l ≫ f.hom.hom) ↔ HasLimit χ g l := by
  refine ⟨fun hl => ?_, HasLimit.comp_hom χ f⟩
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  obtain ⟨l', hl', h⟩ := hl.exists_of_isClosedSubgroup χ f hf
  rwa [(cancel_mono f.hom.hom).mp h] at hl'

/-- For a closed subgroup `f : H ⟶ G`, `P_H(χ) = f⁻¹ P_G(χ ≫ f)`. -/
theorem parabolic_eq_comap_of_isClosedSubgroup (hf : IsClosedSubgroup f) :
    parabolic χ = (parabolic (χ ≫ f)).comap f := by
  refine le_antisymm (parabolic_le_comap χ f) fun T g hg => ?_
  obtain ⟨e, he⟩ := hg
  obtain ⟨e', he', -⟩ := he.exists_of_isClosedSubgroup χ f hf
  exact ⟨e', he'⟩

/-- For a closed subgroup `f : H ⟶ G`, `U_H(χ) = f⁻¹ U_G(χ ≫ f)`. -/
theorem unipotent_eq_comap_of_isClosedSubgroup (hf : IsClosedSubgroup f) :
    unipotent χ = (unipotent (χ ≫ f)).comap f := by
  refine le_antisymm (unipotent_le_comap χ f) fun T g hg => ?_
  have h : HasLimit (χ ≫ f) (g ≫ f.hom.hom) (1 ≫ f.hom.hom) := by
    rw [MonObj.one_comp]
    exact hg
  exact (hasLimit_comp_hom_iff χ f hf).mp h

/-- For a closed subgroup `f : H ⟶ G`, `Z_H(χ) = f⁻¹ Z_G(χ ≫ f)`. -/
theorem centralizer_eq_comap_of_isClosedSubgroup (hf : IsClosedSubgroup f) :
    centralizer χ = (centralizer (χ ≫ f)).comap f := by
  have : IsClosedImmersion f.hom.hom.left := hf
  have : Mono f.hom.hom := Over.mono_of_mono_left _
  exact centralizer_eq_comap_of_mono χ f

/-- For a closed subgroup `f : H ⟶ G`, `H ∩ P_G(χ ≫ f)` is the image of `P_H(χ)`. -/
theorem range_inf_parabolic (hf : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ parabolic (χ ≫ f) = (parabolic χ).map f := by
  rw [parabolic_eq_comap_of_isClosedSubgroup χ f hf, SubgroupFunctor.map_comap]

/-- For a closed subgroup `f : H ⟶ G`, `H ∩ U_G(χ ≫ f)` is the image of `U_H(χ)`. -/
theorem range_inf_unipotent (hf : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ unipotent (χ ≫ f) = (unipotent χ).map f := by
  rw [unipotent_eq_comap_of_isClosedSubgroup χ f hf, SubgroupFunctor.map_comap]

/-- For a closed subgroup `f : H ⟶ G`, `H ∩ Z_G(χ ≫ f)` is the image of `Z_H(χ)`. -/
theorem range_inf_centralizer (hf : IsClosedSubgroup f) :
    SubgroupFunctor.range f ⊓ centralizer (χ ≫ f) = (centralizer χ).map f := by
  rw [centralizer_eq_comap_of_isClosedSubgroup χ f hf, SubgroupFunctor.map_comap]

end Dynamic

end Langlands.GroupScheme
