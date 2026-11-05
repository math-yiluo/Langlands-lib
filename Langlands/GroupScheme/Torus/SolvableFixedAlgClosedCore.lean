import Langlands.GroupScheme.Torus.SolvableFixedContainmentConnectedStatement
import Langlands.GroupScheme.Dynamic.TriangularCell
import Langlands.GroupScheme.Dynamic.GeneralLinearTriangularDiagonal
import Langlands.GroupScheme.Absolute.SolvableTriangularEmbeddingProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.AutomorphicAction.SemidirectSubgroup
import Langlands.GroupScheme.AutomorphicAction.SemidirectDynamic
import Langlands.GroupScheme.Rational.GenericTorusCocharacter
import Langlands.GroupScheme.Rational.SolvableSchemeComparison
import Langlands.GroupScheme.Dynamic.IdentityComponent
import Langlands.GroupScheme.Dynamic.ActionLimitMap
import Langlands.GroupScheme.Dynamic.ActionLieContainment
import Langlands.GroupScheme.Dynamic.CommonTorusIntersections
import Langlands.GroupScheme.Absolute.LieKolchinRationalTriangularization
import Langlands.GroupScheme.RepresentedActionFixed
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # Connectedness of solvable invariant subgroups over an algebraically closed field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace IdentityComponent

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]

/-- A rational point lies in the range of the identity-component inclusion exactly when its
location lies in the connected component of the identity point. -/
theorem mem_range_identityComponentι_iff
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) :
    x ∈ (SubgroupFunctor.range (identityComponentι G)).carrier _ ↔
      RationalZariski.location G x ∈ identitySet G := by
  constructor
  · intro hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    change _ ∈ connectedComponent (identityPoint G)
    rw [← range_identityComponentι]
    exact ⟨y.left (IsLocalRing.closedPoint k), rfl⟩
  · intro hx
    refine SubgroupFunctor.mem_range.mpr
      ⟨FiniteEtaleImage.liftOver (identityComponentι G).hom.hom x ?_,
        FiniteEtaleImage.liftOver_fac _ _ _⟩
    rintro _ ⟨z, rfl⟩
    rw [range_identityComponentι]
    change _ ∈ connectedComponent (identityPoint G) at hx
    have hz : z = IsLocalRing.closedPoint k :=
      @Subsingleton.elim (Spec (CommRingCat.of k)) _ z _
    rw [hz]
    exact hx

/-- Over an algebraically closed field, a smooth affine group all of whose rational points lie
in the identity component is connected (Jacobson property). -/
theorem connectedSpace_of_forall_mem_range [IsAlgClosed k]
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
      x ∈ (SubgroupFunctor.range (identityComponentι G)).carrier _) :
    ConnectedSpace G.X.left := by
  have : JacobsonSpace G.X.left := LocallyOfFiniteType.jacobsonSpace G.X.hom
  have huniv : identitySet G = Set.univ := by
    by_contra hne
    have hZ : (identitySet G)ᶜ.Nonempty := by
      rw [Set.nonempty_compl]
      exact hne
    obtain ⟨p, hpZ, hp⟩ := nonempty_inter_closedPoints hZ
      (isClopen_identitySet G).isClosed.isOpen_compl.isLocallyClosed
    rw [← RationalZariski.range_location] at hp
    obtain ⟨x, rfl⟩ := hp
    exact hpZ ((mem_range_identityComponentι_iff x).1 (h x))
  rw [connectedSpace_iff_univ, ← huniv]
  exact isConnected_connectedComponent

end IdentityComponent

namespace AutomorphicAction

variable {k : Type u} [Field k] {C : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth C.X.hom] [IsAffineHom C.X.hom]
  (b : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp C)

/-- If the fixed points of a `𝔾_m`-action lie in the identity component, then so do the points
whose orbit extends to the affine line: such a point is a limit-preserving product of an
identity-limit point and its fixed limit. -/
theorem parabolic_le_identityComponent_of_centralizer_le {T : Over (Spec (CommRingCat.of k))}
    (hZ : ∀ l ∈ b.centralizer.carrier T,
      l ∈ (SubgroupFunctor.range (identityComponentι C)).carrier T)
    {p : T ⟶ C.X} (hp : p ∈ b.parabolic.carrier T) :
    p ∈ (SubgroupFunctor.range (identityComponentι C)).carrier T := by
  obtain ⟨l, hl⟩ := b.exists_hasLimit hp
  have hlZ := hl.mem_centralizer b
  have hlinv : b.HasLimit l⁻¹ l⁻¹ :=
    b.hasLimit_of_mem_centralizer ((b.centralizer.carrier T).inv_mem hlZ)
  have hU : p * l⁻¹ ∈ b.unipotent.carrier T := by
    rw [mem_unipotent]
    simpa only [mul_inv_cancel] using hl.mul b hlinv
  have h1 := b.unipotent_le_identityComponent T hU
  simpa only [inv_mul_cancel_right] using
    (SubgroupFunctor.range (identityComponentι C)).carrier T |>.mul_mem h1 (hZ l hlZ)

end AutomorphicAction

namespace SolvableFixedCore

open AutomorphicAction

variable {k : Type u} [Field k]

local instance gmIsAffineHom : IsAffineHom (Gm (Spec (CommRingCat.of k))).X.hom :=
  isSplitTorus_gm.isAffineHom

local instance gmSmooth : Smooth (Gm (Spec (CommRingCat.of k))).X.hom := smooth_gm _

local instance gmConnected : ConnectedSpace (Gm (Spec (CommRingCat.of k))).X.left :=
  isSplitTorus_gm.connectedSpace

local instance gmGeometricallyConnected :
    GeometricallyConnected (Gm (Spec (CommRingCat.of k))).X.hom :=
  geometricallyConnected_of_connected _

variable {H : GroupScheme (Spec (CommRingCat.of k))} [Smooth H.X.hom] [IsAffineHom H.X.hom]
  (a : AutomorphicAction (Gm (Spec (CommRingCat.of k))).toGrp H)

local instance semidirectConnected [ConnectedSpace H.X.left] :
    ConnectedSpace a.semidirectProduct.X.left := by
  change ConnectedSpace ↥(CategoryTheory.Limits.pullback H.X.hom
    (Gm (Spec (CommRingCat.of k))).X.hom)
  infer_instance

local instance semidirectIsAffine : IsAffine a.semidirectProduct.X.left :=
  isAffine_of_isAffineHom a.semidirectProduct.X.hom

/-- The unit section of a group scheme is its identity point over the base. -/
theorem one_eq_unit (M : GroupScheme (Spec (CommRingCat.of k))) :
    (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ M.X) = η[M.X] := by
  rw [Hom.one_def, toUnit_unit, Category.id_comp]

omit [Smooth H.X.hom] [IsAffineHom H.X.hom] in
/-- The centralizer of the acting factor in `H ⋊ 𝔾_m` lies in the semidirect subgroup of
every stable subgroup functor containing the fixed points. -/
theorem centralizer_le_semidirectSubgroup {F : SubgroupFunctor H} (hF : a.IsStable F)
    (hfix : a.fixedSubgroup ≤ F) :
    Dynamic.centralizer a.semidirectInr ≤ a.semidirectSubgroup F hF := by
  intro T z hz
  rw [mem_semidirectSubgroup]
  have hdec := a.semidirect_point_decomposition z
  have ht : (a.semidirectPointsEquiv T z).right ≫ a.semidirectInr.hom.hom ∈
      (Dynamic.centralizer a.semidirectInr).carrier T :=
    a.range_semidirectInr_le_centralizer T (SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩)
  have hh : (a.semidirectPointsEquiv T z).left ≫ a.semidirectInl.hom.hom ∈
      (Dynamic.centralizer a.semidirectInr).carrier T := by
    rw [eq_mul_inv_of_mul_eq hdec.symm]
    exact (Dynamic.centralizer a.semidirectInr).carrier T |>.mul_mem hz
      ((Dynamic.centralizer a.semidirectInr).carrier T |>.inv_mem ht)
  have hfixed : (a.semidirectPointsEquiv T z).left ∈ (a.restrict (𝟙 _)).centralizer.carrier T := by
    rw [a.semidirect_centralizer_eq_comap (𝟙 _), SubgroupFunctor.mem_comap, Category.id_comp]
    exact hh
  rw [restrict_id] at hfixed
  exact hfix T hfixed

/-- **Fixed points in the identity component.** Let `a` be a `𝔾_m`-action on a smooth connected
affine group `H`, `F` a stable subgroup functor containing the fixed points, and `q : C → H` a
closed representative of `F` with `C` smooth. Every rational fixed point of the induced action
on `C` lies in the identity component of `C`. -/
theorem centralizer_mem_identityComponent [ConnectedSpace H.X.left] {F : SubgroupFunctor H}
    (hF : a.IsStable F) (hfix : a.fixedSubgroup ≤ F)
    {C : GroupScheme (Spec (CommRingCat.of k))} (q : C ⟶ H) (hq : F.IsRepresentedBy q)
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    {l : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X}
    (hl : l ∈ (a.onRepresentedSubgroup q hq hF).centralizer.carrier _) :
    l ∈ (SubgroupFunctor.range (identityComponentι C)).carrier _ := by
  let σ := a.semidirectInr
  let w := Dynamic.Affine.centralizerHom σ
  have hw := Dynamic.Affine.isRepresentedBy_centralizerHom σ
  have hWconn : ConnectedSpace (Dynamic.Affine.centralizerScheme σ).X.left :=
    ((dynamicConnected k a.semidirectProduct σ _ w).2 inferInstance).2 hw
  let i' := a.semidirectSubgroupInclusion F hF q hq
  have hi' := a.isRepresentedBy_semidirectSubgroupInclusion F hF q hq
  have hmono : Mono i'.hom.hom := hi'.1
  have hrange : SubgroupFunctor.range w ≤ a.semidirectSubgroup F hF := by
    rw [hw.2]
    exact centralizer_le_semidirectSubgroup a hF hfix
  let f := hi'.factorHom w hrange
  have hf : f ≫ i' = w := hi'.factorHom_comp w hrange
  -- the image of `l` in `H ⋊ 𝔾_m` is a centralizing point
  change l ∈ (a.onRepresentedSubgroup q hq hF).fixedSubgroup.carrier _ at hl
  rw [onRepresentedSubgroup_fixedSubgroup_eq_comap, SubgroupFunctor.mem_comap] at hl
  have hlZ : (l ≫ q.hom.hom) ≫ a.semidirectInl.hom.hom ∈
      (Dynamic.centralizer σ).carrier _ := by
    have h : l ≫ q.hom.hom ∈ (a.restrict (𝟙 _)).centralizer.carrier _ := by
      rw [restrict_id]
      exact hl
    rw [a.semidirect_centralizer_eq_comap (𝟙 _), SubgroupFunctor.mem_comap,
      Category.id_comp] at h
    exact h
  rw [← hw.2] at hlZ
  obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hlZ
  have hinl : (l ≫ (a.onRepresentedSubgroup q hq hF).semidirectInl.hom.hom) ≫ i'.hom.hom =
      (l ≫ q.hom.hom) ≫ a.semidirectInl.hom.hom := by
    apply (a.semidirectPointsEquiv _).injective
    dsimp only [i', semidirectSubgroupInclusion]
    rw [semidirectMap_points, semidirectInl_points, semidirectInl_points]
    rfl
  have hzf : z ≫ f.hom.hom = l ≫ (a.onRepresentedSubgroup q hq hF).semidirectInl.hom.hom := by
    rw [← cancel_mono i'.hom.hom, hinl, ← hz, Category.assoc, ← Grp.comp_hom_hom, hf]
  -- the connected centralizer maps into the identity component of `C`
  let a' := a.onRepresentedSubgroup q hq hF
  let π := (a'.semidirectPointsEquiv a'.semidirectProduct.X (𝟙 _)).left
  have hπ : ∀ {T : Over (Spec (CommRingCat.of k))} (x : T ⟶ a'.semidirectProduct.X),
      x ≫ π = (a'.semidirectPointsEquiv T x).left := fun x => by
    have h := (a'.semidirectPointsEquiv_naturality x (𝟙 _)).1
    rw [Category.comp_id] at h
    exact h.symm
  let g := f.hom.hom ≫ π
  have hg : η[(Dynamic.Affine.centralizerScheme σ).X] ≫ g = η[C.X] := by
    rw [← one_eq_unit, ← one_eq_unit]
    change (1 : _ ⟶ _) ≫ f.hom.hom ≫ π = 1
    rw [← Category.assoc, MonObj.one_comp, hπ, map_one]
    rfl
  have hsub := IdentityComponent.range_subset_identitySet C g
    η[(Dynamic.Affine.centralizerScheme σ).X] hg
  rw [IdentityComponent.mem_range_identityComponentι_iff]
  have hlg : l = z ≫ g := by
    change l = z ≫ f.hom.hom ≫ π
    rw [← Category.assoc, hzf, hπ, semidirectInl_points]
    rfl
  rw [hlg]
  exact hsub ⟨_, rfl⟩

omit [Smooth H.X.hom] [IsAffineHom H.X.hom] in
/-- The acting factor of `H ⋊ 𝔾_m` is carried by the inclusion of the semidirect product of a
stable represented subgroup. -/
theorem semidirectInr_comp_semidirectSubgroupInclusion {F : SubgroupFunctor H}
    (hF : a.IsStable F) {C : GroupScheme (Spec (CommRingCat.of k))} (q : C ⟶ H)
    (hq : F.IsRepresentedBy q) :
    (a.onRepresentedSubgroup q hq hF).semidirectInr ≫ a.semidirectSubgroupInclusion F hF q hq =
      a.semidirectInr := by
  refine hom_ext_points fun T t => ?_
  apply (a.semidirectPointsEquiv T).injective
  dsimp only [semidirectSubgroupInclusion]
  rw [Grp.comp_hom_hom, ← Category.assoc, semidirectMap_points, semidirectInr_points,
    semidirectInr_points]
  exact SemidirectProduct.ext (MonObj.one_comp _) rfl

/-- The multiplicative group has commutative points, so the derived series stops at step one
on every test scheme. -/
theorem isSolvableScheme_gm (S : Scheme.{u}) : RelativeRoot.IsSolvableScheme (Gm S).toGrp :=
  ⟨1, fun _ => by rw [derivedSeries_one]; exact commutator_eq_bot _⟩

/-- **Rational points in the identity component.** In the setting of
`centralizer_mem_identityComponent`, assume moreover that `H` is solvable for all tests and that
the field is algebraically closed. Then every rational point of `C` lies in the identity
component of `C`. -/
theorem rational_mem_identityComponent [IsAlgClosed k] [ConnectedSpace H.X.left]
    (hsolv : RelativeRoot.IsSolvableScheme H) {F : SubgroupFunctor H}
    (hF : a.IsStable F) (hfix : a.fixedSubgroup ≤ F)
    {C : GroupScheme (Spec (CommRingCat.of k))} (q : C ⟶ H) (hq : F.IsRepresentedBy q)
    (hqc : IsClosedSubgroup q) [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) :
    x ∈ (SubgroupFunctor.range (identityComponentι C)).carrier _ := by
  -- a closed upper triangular embedding of `H ⋊ 𝔾_m` with diagonal acting factor
  have hAsolv : IsSolvableGroupScheme a.semidirectProduct :=
    (RelativeRoot.isSolvableScheme_semidirect a (isSolvableScheme_gm _) hsolv).isSolvableGroupScheme
  obtain ⟨N, j, hj⟩ := solvableTriangularEmbeddingStatement k a.semidirectProduct hAsolv
  let e₀ : Fin N → ℤ := fun i => -(i.val : ℤ)
  let ρ₀ := j ≫ GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e₀
  have hρ₀ : ∀ (T : Over (Spec (CommRingCat.of k))) (y : T ⟶ a.semidirectProduct.X),
      y ≫ ρ₀.hom.hom ∈ (GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e₀).carrier T := by
    intro T y
    rw [← (GeneralLinear.isRepresentedBy_blockParabolic (Fin N) (CommRingCat.of k) e₀).2]
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ j.hom.hom, by rw [Grp.comp_hom_hom, Category.assoc]⟩
  obtain ⟨g, e, hg, he⟩ := GeneralLinear.exists_triangular_innerIso_comp_eq_diagonalCocharacter k
    (a.semidirectInr ≫ ρ₀) (fun T t => by
      rw [Grp.comp_hom_hom, ← Category.assoc]
      exact hρ₀ T _)
  let κ := (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).innerIso g
  -- the induced embedding of `C ⋊ 𝔾_m`
  let a' := a.onRepresentedSubgroup q hq hF
  let i' := a.semidirectSubgroupInclusion F hF q hq
  let ρ := i' ≫ ρ₀ ≫ κ.hom
  have : IsClosedImmersion i'.hom.hom.left :=
    a.isClosedSubgroup_semidirectSubgroupInclusion F hF q hq hqc
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e₀).hom.hom.left :=
    GeneralLinear.isClosedSubgroup_blockParabolicHom (Fin N) (CommRingCat.of k) e₀
  have : IsIso κ.hom.hom.hom.left :=
    (inferInstance : IsIso ((Over.forget _).mapIso ((Grp.forget _).mapIso κ)).hom)
  have : IsClosedImmersion ρ.hom.hom.left :=
    (inferInstance : IsClosedImmersion (i'.hom.hom.left ≫ j.hom.hom.left ≫
      (GeneralLinear.blockParabolicHom (Fin N) (CommRingCat.of k) e₀).hom.hom.left ≫
        κ.hom.hom.hom.left))
  have hρ : a'.semidirectInr ≫ ρ = GeneralLinear.diagonalCocharacter (Fin N) (CommRingCat.of k) e := by
    change a'.semidirectInr ≫ i' ≫ ρ₀ ≫ κ.hom = _
    rw [← Category.assoc, semidirectInr_comp_semidirectSubgroupInclusion, ← Category.assoc]
    exact he
  -- the cell decomposition of the image of `x`
  let y := x ≫ a'.semidirectInl.hom.hom
  have hcell : IsUnit (GeneralLinear.cellMinor e (GeneralLinear.pointsEquiv (Fin N) _ _
      (y ≫ ρ.hom.hom)).val) := by
    apply GeneralLinear.isUnit_cellMinor_of_mem_blockParabolicSubgroup
    have hc : GeneralLinear.pointsEquiv (Fin N) _ _
        ((GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)).constantPoint g
          (Over.mk (𝟙 (Spec (CommRingCat.of k))))) ∈
        GeneralLinear.blockParabolicSubgroup _ e₀ :=
      (GeneralLinear.mem_blockParabolic e₀).1
        ((GeneralLinear.blockParabolic (Fin N) (CommRingCat.of k) e₀).comp_mem _ hg)
    have hm : GeneralLinear.pointsEquiv (Fin N) _ _ ((y ≫ i'.hom.hom) ≫ ρ₀.hom.hom) ∈
        GeneralLinear.blockParabolicSubgroup _ e₀ :=
      (GeneralLinear.mem_blockParabolic e₀).1 (hρ₀ _ _)
    have hy : y ≫ ρ.hom.hom = ((y ≫ i'.hom.hom) ≫ ρ₀.hom.hom) ≫ κ.hom.hom.hom := by
      simp only [ρ, Grp.comp_hom_hom, Category.assoc]
    rw [hy, comp_innerIso_hom, map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc hm) (Subgroup.inv_mem _ hc)
  obtain ⟨p, hp, hu⟩ := Dynamic.exists_mem_parabolic_of_isUnit_cellMinor hρ y hcell
  -- the unipotent factor comes from `C`
  let χ := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1))
  obtain ⟨u₀, hu₀⟩ := SubgroupFunctor.mem_range.mp (a'.semidirect_unipotent_le_range χ _ hu)
  have hu₀C : u₀ ∈ (SubgroupFunctor.range (identityComponentι C)).carrier _ := by
    apply (a'.restrict χ).unipotent_le_identityComponent
    rw [a'.semidirect_unipotent_eq_comap χ, SubgroupFunctor.mem_comap, hu₀]
    exact hu
  -- the parabolic factor comes from `C`
  let p₀ := u₀⁻¹ * x
  have hp₀ : p₀ ≫ a'.semidirectInl.hom.hom = p := by
    change (u₀⁻¹ * x) ≫ a'.semidirectInl.hom.hom = p
    rw [MonObj.mul_comp, GrpObj.inv_comp, hu₀]
    change (y * p⁻¹)⁻¹ * y = p
    group
  have hp₀P : p₀ ∈ a'.parabolic.carrier _ := by
    have h : p₀ ∈ (a'.restrict (𝟙 _)).parabolic.carrier _ := by
      rw [a'.semidirect_parabolic_eq_comap (𝟙 _), SubgroupFunctor.mem_comap, Category.id_comp,
        hp₀]
      exact hp
    rwa [restrict_id] at h
  have hp₀C := a'.parabolic_le_identityComponent_of_centralizer_le
    (fun l hl => centralizer_mem_identityComponent a hF hfix q hq hl) hp₀P
  have hx : x = u₀ * p₀ := by
    change x = u₀ * (u₀⁻¹ * x)
    group
  rw [hx]
  exact Subgroup.mul_mem _ hu₀C hp₀C

end SolvableFixedCore

namespace Torus

/-- **Connected invariant subgroups, algebraically closed case.** Over an algebraically closed
field, let a split torus `S` act on a smooth connected affine group `H` that is solvable for all
tests. A subgroup functor `F` that is stable, contains the fixed subgroup and is represented by a
smooth closed subgroup `q : C → H` has connected representative `C`. -/
theorem connectedSpace_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (H : GroupScheme (Spec (CommRingCat.of k))) (hHs : Smooth H.X.hom)
    (hHa : IsAffineHom H.X.hom) (hHc : ConnectedSpace H.X.left)
    (hsolv : RelativeRoot.IsSolvableScheme H)
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (c : AutomorphicAction S.toGrp H) (F : SubgroupFunctor H) (hF : c.IsStable F)
    (hfix : c.fixedSubgroup ≤ F)
    (C : GroupScheme (Spec (CommRingCat.of k))) (q : C ⟶ H) (hq : F.IsRepresentedBy q)
    (hqc : IsClosedSubgroup q) (hCs : Smooth C.X.hom) :
    ConnectedSpace C.X.left := by
  obtain ⟨ν, hν⟩ := AutomorphicAction.exists_cocharacter_fixedSubgroup hS c
  let a := c.restrict (CommGroupScheme.groupHom ν)
  have haF : a.IsStable F := hF.restrict _
  have hafix : a.fixedSubgroup ≤ F := by
    change (c.restrict (CommGroupScheme.groupHom ν)).fixedSubgroup ≤ F
    rw [hν]
    exact hfix
  have : IsClosedImmersion q.hom.hom.left := hqc
  have : IsAffineHom C.X.hom := by
    rw [← Over.w q.hom.hom]
    infer_instance
  exact IdentityComponent.connectedSpace_of_forall_mem_range fun x =>
    SolvableFixedCore.rational_mem_identityComponent a hsolv haF hafix q hq hqc x

end Torus

end Langlands.GroupScheme
