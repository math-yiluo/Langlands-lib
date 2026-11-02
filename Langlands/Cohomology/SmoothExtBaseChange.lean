import Langlands.Cohomology.HyperextExtBaseChange
import Langlands.Cohomology.HyperextInvariantsLocalization
import Langlands.Cohomology.DivisibleSystem.PermutationProjective

/-!
# Extension of scalars on `Ext` groups of smooth representations

The Library's `smoothExtBaseChangeMap R S G X Y n` compares `S ⊗[R] Ext^n_G(X, Y)` with
`Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` for smooth representations of a topological group `G`. This module
provides a class of projective smooth representations to which the dimension-shifting theorems of
`Langlands.Cohomology.HyperextExtBaseChange` apply: representations free of finite rank on
vectors fixed by a pro-`p` subgroup, for `p` invertible in `R` and assuming
`ProPInvariantsExactStatement`. For a localization `S` of `R` it proves that the comparison map is
injective, respectively bijective, when `X` has a resolution of length `n`, respectively `n + 1`,
by such representations.

* `IsFreeOnFixedVectors H x`: the `H`-fixed vectors `x i` freely generate `P` among smooth
  representations; `IsFreeOnFixedVectors.eval_bijective`, `HasFreeFixedBasis H P` and
  `HasProPFreeFixedBasis p P`, with their resolutions of every length.
* `exists_mem_invariants_of_epi`, `IsFreeOnFixedVectors.projective`,
  `HasProPFreeFixedBasis.projective`: projectivity, given `ProPInvariantsExactStatement`.
* `isFreeOnFixedVectors_compactInduction`, `hasProPFreeFixedBasis_compactInduction`: compact
  induction `c-Ind_H^G M` from an open subgroup of the trivial representation on a free module.
* `smoothRepRestrictScalars_preservesEpimorphisms`, `IsFreeOnFixedVectors.smoothRepExtendScalars`,
  `HasProPFreeFixedBasis.projective_smoothRepExtendScalars`: behaviour under extension of
  scalars.
* `smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors` and
  `smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis`: the comparison map on `Hom` for a
  localization `S`.
* `smoothExtBaseChangeMap_injective_of_hasResolutionBy`,
  `smoothExtBaseChangeMap_bijective_of_hasResolutionBy` and the linear equivalence
  `smoothExtBaseChangeEquivOfHasResolutionBy`: the comparison map on `Ext`.

`ProPInvariantsExactStatement` and the existence of the resolutions remain hypotheses.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

universe w uR uS uG uV t t'

namespace HyperextScalarExtension

section FixedVectors

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A morphism of smooth representations sends vectors fixed by a subgroup `H` to vectors fixed
by `H`. -/
theorem smoothRepHom_mem_invariants (H : Subgroup G) {A B : SmoothRep.{uR, uG, w} R G}
    (f : A ⟶ B) {v : A} (hv : v ∈ Representation.invariants (A.representation.comp H.subtype)) :
    SmoothRep.hom f v ∈ Representation.invariants (B.representation.comp H.subtype) := by
  refine (Representation.mem_invariants _ _).2 fun h => ?_
  change B.representation (h : G) (SmoothRep.hom f v) = SmoothRep.hom f v
  rw [← Representation.IntertwiningMap.isIntertwining _ _ (SmoothRep.hom f) (h : G) v]
  exact congrArg (SmoothRep.hom f) ((Representation.mem_invariants _ v).1 hv h)

/-- `IsFreeOnFixedVectors H x`: the family `x` of vectors of a smooth representation `P` of `G`
is fixed by the subgroup `H` and freely generates `P` among smooth representations with
`H`-fixed generators. That is, every `x i` is fixed by `H`, morphisms `P ⟶ Y` of smooth
representations agreeing on all `x i` are equal, and for every family `y` of `H`-fixed vectors of
a smooth representation `Y` there is a morphism `P ⟶ Y` sending each `x i` to `y i`. For an open
subgroup `H`, the compact induction `c-Ind_H^G M` of the trivial representation on a free
`R`-module `M` is an example (`isFreeOnFixedVectors_compactInduction`). -/
structure IsFreeOnFixedVectors (H : Subgroup G) {P : SmoothRep.{uR, uG, w} R G} {ι : Type*}
    (x : ι → P) : Prop where
  mem_invariants : ∀ i, x i ∈ Representation.invariants (P.representation.comp H.subtype)
  hom_ext : ∀ {Y : SmoothRep.{uR, uG, w} R G} {f g : P ⟶ Y},
    (∀ i, SmoothRep.hom f (x i) = SmoothRep.hom g (x i)) → f = g
  exists_hom : ∀ {Y : SmoothRep.{uR, uG, w} R G} (y : ι → Y),
    (∀ i, y i ∈ Representation.invariants (Y.representation.comp H.subtype)) →
      ∃ f : P ⟶ Y, ∀ i, SmoothRep.hom f (x i) = y i

/-- For `x` free on `H`-fixed vectors, evaluation at `x` is a bijection from the morphisms
`P ⟶ Y` to the families of `H`-fixed vectors of `Y`. -/
theorem IsFreeOnFixedVectors.eval_bijective {H : Subgroup G} {P : SmoothRep.{uR, uG, w} R G}
    {ι : Type*} {x : ι → P} (hx : IsFreeOnFixedVectors H x) (Y : SmoothRep.{uR, uG, w} R G) :
    Function.Bijective (fun (f : P ⟶ Y) (i : ι) =>
      (⟨SmoothRep.hom f (x i), smoothRepHom_mem_invariants H f (hx.mem_invariants i)⟩ :
        Representation.invariants (Y.representation.comp H.subtype))) := by
  refine ⟨fun f g h => hx.hom_ext fun i => congrArg Subtype.val (congrFun h i), fun y => ?_⟩
  obtain ⟨f, hf⟩ := hx.exists_hom (fun i => (y i : Y)) fun i => (y i).2
  exact ⟨f, funext fun i => Subtype.ext (hf i)⟩

/-- A zero object is free on the empty family, for every subgroup `H`. -/
theorem isFreeOnFixedVectors_of_isZero (H : Subgroup G) {Z : SmoothRep.{uR, uG, w} R G}
    (hZ : IsZero Z) : IsFreeOnFixedVectors H (Fin.elim0 : Fin 0 → Z) where
  mem_invariants i := i.elim0
  hom_ext _ := hZ.eq_of_src _ _
  exists_hom _ _ := ⟨0, fun i => i.elim0⟩

/-- `HasFreeFixedBasis H P`: `P` is free of finite rank on `H`-fixed vectors, that is, there is a
family `x : Fin n → P` with `IsFreeOnFixedVectors H x`. -/
def HasFreeFixedBasis (H : Subgroup G) (P : SmoothRep.{uR, uG, w} R G) : Prop :=
  ∃ (n : ℕ) (x : Fin n → P), IsFreeOnFixedVectors H x

/-- `HasProPFreeFixedBasis p P`: `P` is free of finite rank on vectors fixed by some pro-`p`
subgroup `H` of `G`. -/
def HasProPFreeFixedBasis (p : ℕ) (P : SmoothRep.{uR, uG, w} R G) : Prop :=
  ∃ H : Subgroup G, IsProPSubgroup p H ∧ HasFreeFixedBasis H P

/-- A zero object is free of rank `0` on `H`-fixed vectors. -/
theorem hasFreeFixedBasis_of_isZero (H : Subgroup G) {Z : SmoothRep.{uR, uG, w} R G}
    (hZ : IsZero Z) : HasFreeFixedBasis H Z :=
  ⟨0, Fin.elim0, isFreeOnFixedVectors_of_isZero H hZ⟩

/-- A representation free of finite rank on `H`-fixed vectors has resolutions of every length by
such representations. -/
theorem HasFreeFixedBasis.hasResolutionBy {H : Subgroup G} {P : SmoothRep.{uR, uG, w} R G}
    (hP : HasFreeFixedBasis H P) (n : ℕ) : HasResolutionBy (HasFreeFixedBasis H) n P :=
  HasResolutionBy.of_prop (isZero_zero _) (hasFreeFixedBasis_of_isZero H (isZero_zero _)) n hP

/-- A representation free of finite rank on vectors fixed by a pro-`p` subgroup has resolutions
of every length by such representations. -/
theorem HasProPFreeFixedBasis.hasResolutionBy {p : ℕ} {P : SmoothRep.{uR, uG, w} R G}
    (hP : HasProPFreeFixedBasis p P) (n : ℕ) : HasResolutionBy (HasProPFreeFixedBasis p) n P := by
  obtain ⟨H, hH, hPH⟩ := hP
  exact (hPH.hasResolutionBy n).mono fun _ hQ => ⟨H, hH, hQ⟩

variable [IsTopologicalGroup G]

/-- Given `ProPInvariantsExactStatement`, an epimorphism of smooth representations is surjective
on vectors fixed by a pro-`p` subgroup `H`, for `p` invertible in `R`. -/
theorem exists_mem_invariants_of_epi (hP : ProPInvariantsExactStatement.{uG, uR, w}) {p : ℕ}
    {H : Subgroup G} (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
    {Y Z : SmoothRep.{uR, uG, w} R G} (e : Y ⟶ Z) [Epi e] {z : Z}
    (hz : z ∈ Representation.invariants (Z.representation.comp H.subtype)) :
    ∃ y ∈ Representation.invariants (Y.representation.comp H.subtype), SmoothRep.hom e y = z := by
  have := hH.compactSpace
  have := hH.totallyDisconnectedSpace
  have := smoothInvariantsFunctor_preservesEpimorphisms R H hP hH.prime hH.isPGroup hR
  have h := (ModuleCat.epi_iff_surjective _).1
    ((smoothInvariantsFunctor.{uR, uG, w} R H).map_epi
      ((Induction.smoothRestriction.{uR, uG, w} R H).map e))
  obtain ⟨⟨y, hy⟩, hyz⟩ := h ⟨z, hz⟩
  exact ⟨y, hy, congrArg Subtype.val hyz⟩

/-- Given `ProPInvariantsExactStatement`, a smooth representation free on vectors fixed by a
pro-`p` subgroup is projective, for `p` invertible in `R`. -/
theorem IsFreeOnFixedVectors.projective (hP : ProPInvariantsExactStatement.{uG, uR, w}) {p : ℕ}
    {H : Subgroup G} (hH : IsProPSubgroup p H) (hR : IsUnit (p : R))
    {P : SmoothRep.{uR, uG, w} R G} {ι : Type*} {x : ι → P} (hx : IsFreeOnFixedVectors H x) :
    Projective P where
  factors {Y Z} f e _ := by
    choose y hy hye using fun i =>
      exists_mem_invariants_of_epi hP hH hR e (smoothRepHom_mem_invariants H f (hx.mem_invariants i))
    obtain ⟨g, hg⟩ := hx.exists_hom y hy
    refine ⟨g, hx.hom_ext fun i => ?_⟩
    change SmoothRep.hom e (SmoothRep.hom g (x i)) = _
    rw [hg, hye]

/-- Given `ProPInvariantsExactStatement`, a smooth representation free of finite rank on vectors
fixed by a pro-`p` subgroup is projective, for `p` invertible in `R`. -/
theorem HasProPFreeFixedBasis.projective (hP : ProPInvariantsExactStatement.{uG, uR, w})
    {p : ℕ} (hR : IsUnit (p : R)) {P : SmoothRep.{uR, uG, w} R G}
    (hPp : HasProPFreeFixedBasis p P) : Projective P := by
  obtain ⟨H, hH, n, x, hx⟩ := hPp
  exact hx.projective hP hH hR

end FixedVectors

section CompactInduction

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (H : Subgroup G) (hH : IsOpen (H : Set G))

/-- For an open subgroup `H` and an `R`-module `M` with a basis `b`, the compact induction
`c-Ind_H^G M` of the trivial representation of `H` on `M` is free on the `H`-fixed vectors
`1_H ⊗ b i`, the images of the basis vectors under the unit `M → c-Ind_H^G M` of Frobenius
reciprocity (the functions supported on `H` with value `b i` on `H`). -/
theorem isFreeOnFixedVectors_compactInduction {ι : Type*} (M : ModuleCat.{max uG uV} R)
    (b : Module.Basis ι R M) :
    IsFreeOnFixedVectors H
      (P := (Induction.smoothCompactInduction.{uR, uG, uV} R H).obj
        ((smoothTrivialFunctor R H).obj M))
      (fun i => SmoothRep.hom ((Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
        ((smoothTrivialFunctor R H).obj M)) (b i)) where
  mem_invariants i := (Representation.mem_invariants _ _).2 fun h =>
    (Representation.IntertwiningMap.isIntertwining _ _
      (SmoothRep.hom ((Induction.compactInductionAdjunction.{uR, uG, uV} H hH).unit.app
        ((smoothTrivialFunctor R H).obj M))) h (b i)).symm
  hom_ext {Y f g} hfg := by
    let adj := Induction.compactInductionAdjunction.{uR, uG, uV} (R := R) H hH
    refine (adj.homEquiv _ Y).injective (ObjectProperty.hom_ext _ (Rep.hom_ext
      (Representation.IntertwiningMap.ext (b.ext fun i => hfg i))))
  exists_hom {Y} y hy := by
    let adj := Induction.compactInductionAdjunction.{uR, uG, uV} (R := R) H hH
    let A := (smoothTrivialFunctor R H).obj M
    let L : M →ₗ[R] Representation.invariants (Y.representation.comp H.subtype) :=
      b.constr R fun i => ⟨y i, hy i⟩
    let φ : A.representation.IntertwiningMap
        ((Induction.smoothRestriction.{uR, uG, max uG uV} R H).obj Y).representation :=
      { toLinearMap := (Representation.invariants (Y.representation.comp H.subtype)).subtype ∘ₗ L
        isIntertwining' := fun h => LinearMap.ext fun v => ((L v).2 h).symm }
    refine ⟨(adj.homEquiv A Y).symm (SmoothRep.ofHom φ), fun i => ?_⟩
    have h := congrArg (fun T => SmoothRep.hom T (b i))
      ((adj.homEquiv A Y).apply_symm_apply (SmoothRep.ofHom φ))
    exact h.trans (congrArg Subtype.val (b.constr_basis R (fun i =>
      (⟨y i, hy i⟩ : Representation.invariants (Y.representation.comp H.subtype))) i))

include hH in
/-- For an open pro-`p` subgroup `H` and an `R`-module `M` with a basis indexed by `Fin n`, the
compact induction `c-Ind_H^G M` of the trivial representation of `H` on `M` is free of finite
rank on vectors fixed by a pro-`p` subgroup. -/
theorem hasProPFreeFixedBasis_compactInduction {p : ℕ} (hHp : IsProPSubgroup p H) {n : ℕ}
    (M : ModuleCat.{max uG uV} R) (b : Module.Basis (Fin n) R M) :
    HasProPFreeFixedBasis p ((Induction.smoothCompactInduction.{uR, uG, uV} R H).obj
      ((smoothTrivialFunctor R H).obj M)) :=
  ⟨H, hHp, n, _, isFreeOnFixedVectors_compactInduction H hH M b⟩

end CompactInduction

section ExtendScalars

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  {G : Type uG} [Group G] [TopologicalSpace G]

variable (R G) in
/-- Restriction of scalars of smooth representations preserves epimorphisms. -/
instance smoothRepRestrictScalars_preservesEpimorphisms :
    (smoothRepRestrictScalars.{w} R S G).PreservesEpimorphisms where
  preserves {W W'} f _ := by
    have hf := (SmoothRep.epi_iff_surjective f).1 inferInstance
    refine (SmoothRep.epi_iff_surjective _).2 fun x => ?_
    obtain ⟨y, hy⟩ := hf (RestrictScalars.addEquiv R S W' x)
    refine ⟨(RestrictScalars.addEquiv R S W).symm y, ?_⟩
    rw [smoothRepRestrictScalars_map_apply, AddEquiv.apply_symm_apply, hy]
    exact AddEquiv.symm_apply_apply _ _

/-- Extension of scalars preserves freeness on fixed vectors: if `x` is free on `H`-fixed
vectors of `P`, then the vectors `1 ⊗ x i` are free on `H`-fixed vectors of `S ⊗[R] P`. -/
theorem IsFreeOnFixedVectors.smoothRepExtendScalars {H : Subgroup G}
    {P : SmoothRep.{uR, uG, max uS w} R G} {ι : Type*} {x : ι → P}
    (hx : IsFreeOnFixedVectors H x) :
    IsFreeOnFixedVectors H (P := (smoothRepExtendScalars.{max uS w} R S G).obj P)
      (fun i => (1 : S) ⊗ₜ[R] x i) where
  mem_invariants i := (Representation.mem_invariants _ _).2 fun h => by
    change (1 : S) ⊗ₜ[R] P.representation (h : G) (x i) = (1 : S) ⊗ₜ[R] x i
    exact congrArg ((1 : S) ⊗ₜ[R] ·) ((Representation.mem_invariants _ _).1 (hx.mem_invariants i) h)
  hom_ext {Y f g} hfg := by
    let adj := smoothRepExtendScalarsAdjunction.{w} R S G
    exact (adj.homEquiv P Y).injective (hx.hom_ext fun i =>
      congrArg (RestrictScalars.addEquiv R S Y).symm (hfg i))
  exists_hom {Y} y hy := by
    let adj := smoothRepExtendScalarsAdjunction.{w} R S G
    let y' : ι → (smoothRepRestrictScalars R S G).obj Y := fun i =>
      (RestrictScalars.addEquiv R S Y).symm (y i)
    have hy' : ∀ i, y' i ∈ Representation.invariants
        (((smoothRepRestrictScalars R S G).obj Y).representation.comp H.subtype) := fun i =>
      (Representation.mem_invariants _ _).2 fun h => by
        change (RestrictScalars.addEquiv R S Y).symm (Y.representation (h : G)
          (RestrictScalars.addEquiv R S Y ((RestrictScalars.addEquiv R S Y).symm (y i)))) = _
        rw [AddEquiv.apply_symm_apply]
        exact congrArg (RestrictScalars.addEquiv R S Y).symm
          ((Representation.mem_invariants _ _).1 (hy i) h)
    obtain ⟨f, hf⟩ := hx.exists_hom y' hy'
    refine ⟨(adj.homEquiv P Y).symm f, fun i => ?_⟩
    change (1 : S) • RestrictScalars.addEquiv R S Y (SmoothRep.hom f (x i)) = y i
    rw [hf i, AddEquiv.apply_symm_apply, one_smul]

/-- Extension of scalars sends a smooth representation free on vectors fixed by a pro-`p`
subgroup to a projective smooth representation, given `ProPInvariantsExactStatement` and `p`
invertible in `R`. -/
theorem HasProPFreeFixedBasis.projective_smoothRepExtendScalars [IsTopologicalGroup G]
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    {P : SmoothRep.{uR, uG, max uS w} R G} (hPp : HasProPFreeFixedBasis p P) :
    Projective ((smoothRepExtendScalars.{max uS w} R S G).obj P) :=
  (smoothRepExtendScalarsAdjunction.{w} R S G).map_projective P (hPp.projective hP hR)

end ExtendScalars

section Localization

variable {R : Type uR} [CommRing R] (S : Type uS) [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

include M

/-- **Hom groups out of representations free on fixed vectors and localization.** Let `S` be a
localization of `R` and `H` a compact subgroup of `G`. If `P` is free on finitely many `H`-fixed
vectors, then `S ⊗[R] Hom_G(P, Y) → Hom_G(S ⊗[R] P, S ⊗[R] Y)` is bijective for every smooth
representation `Y`: both sides are identified with `n` copies of the `H`-fixed vectors of
`S ⊗[R] Y`, using that taking `H`-fixed vectors commutes with localization for smooth
representations of a compact group. -/
theorem smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors {H : Subgroup G}
    [CompactSpace H] {P : SmoothRep.{uR, uG, max uS w} R G} {n : ℕ} {x : Fin n → P}
    (hx : IsFreeOnFixedVectors H x) (Y : SmoothRep.{uR, uG, max uS w} R G) :
    Function.Bijective (homBaseChangeMap (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) P Y) := by
  let ρ := Y.representation.comp H.subtype
  let eR : (P ⟶ Y) ≃ₗ[R] (Fin n → Representation.invariants ρ) := LinearEquiv.ofBijective
    { toFun := fun f i =>
        ⟨SmoothRep.hom f (x i), smoothRepHom_mem_invariants H f (hx.mem_invariants i)⟩
      map_add' := fun f f' => rfl
      map_smul' := fun r f => rfl }
    (hx.eval_bijective Y)
  let ψ : S ⊗[R] (P ⟶ Y) ≃ₗ[S] (Fin n → S ⊗[R] Representation.invariants ρ) :=
    (eR.baseChange R S _ _).trans
      (TensorProduct.piRight R S S (fun _ : Fin n => Representation.invariants ρ))
  let Φ : (Fin n → S ⊗[R] Representation.invariants ρ) ≃ₗ[S]
      (Fin n → Representation.invariants (baseChangeRepresentation S ρ)) :=
    LinearEquiv.piCongrRight fun _ => invariantsBaseChangeEquivOfIsLocalization S M
      (hasFiniteOrbits_comp_subtype_of_isSmooth Y.isSmooth H)
  let θ : (Fin n → Representation.invariants (baseChangeRepresentation S ρ)) →
      (Fin n → S ⊗[R] Y) := fun v i => (v i : S ⊗[R] Y)
  have hθ : Function.Injective θ := fun v v' h =>
    funext fun i => Subtype.ext (congrFun h i)
  let E : ((smoothRepExtendScalars.{max uS w} R S G).obj P ⟶
      (smoothRepExtendScalars.{max uS w} R S G).obj Y) → (Fin n → S ⊗[R] Y) :=
    fun g i => SmoothRep.hom g ((1 : S) ⊗ₜ[R] x i)
  have hE : Function.Injective E := fun g g' h =>
    (hx.smoothRepExtendScalars S).hom_ext fun i => congrFun h i
  have key : ∀ t, E (homBaseChangeMap (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) P Y t) = θ (Φ (ψ t)) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul s f =>
      funext i
      change s • ((1 : S) ⊗ₜ[R] SmoothRep.hom f (x i)) = s ⊗ₜ[R] SmoothRep.hom f (x i)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    | add a c ha hc =>
      rw [map_add, map_add, map_add]
      funext i
      exact congrArg₂ (· + ·) (congrFun ha i) (congrFun hc i)
  refine ⟨fun t t' h => (Φ.injective.comp ψ.injective) (hθ ?_), fun g => ?_⟩
  · change θ (Φ (ψ t)) = θ (Φ (ψ t'))
    rw [← key, ← key, h]
  · have hg : ∀ i, E g i ∈ Representation.invariants (baseChangeRepresentation S ρ) := fun i =>
      smoothRepHom_mem_invariants H g ((hx.smoothRepExtendScalars S).mem_invariants i)
    refine ⟨ψ.symm (Φ.symm fun i => ⟨E g i, hg i⟩), hE ?_⟩
    rw [key, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

/-- The version of `smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors` for
representations free of finite rank on vectors fixed by a pro-`p` subgroup. -/
theorem smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis {p : ℕ}
    {P : SmoothRep.{uR, uG, max uS w} R G} (hP : HasProPFreeFixedBasis p P)
    (Y : SmoothRep.{uR, uG, max uS w} R G) :
    Function.Bijective (homBaseChangeMap (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) P Y) := by
  obtain ⟨H, hH, n, x, hx⟩ := hP
  have := hH.compactSpace
  exact smoothHomBaseChangeMap_bijective_of_isFreeOnFixedVectors S M hx Y

section Ext

variable [Module.Flat R S] [HasExt.{t} (SmoothRep.{uR, uG, max uS w} R G)]
  [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)] (Y : SmoothRep.{uR, uG, max uS w} R G)

/-- **`Ext` of smooth representations and localization, injectivity.** Assume
`ProPInvariantsExactStatement`, let `p` be invertible in `R` and let `S` be a localization of
`R`. If `X` has a resolution `P_n → ⋯ → P_0 → X → 0` by smooth representations free of finite
rank on vectors fixed by pro-`p` subgroups, then
`S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is injective. -/
theorem smoothExtBaseChangeMap_injective_of_hasResolutionBy
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (HasProPFreeFixedBasis p) n X) :
    Function.Injective (smoothExtBaseChangeMap.{max uS w} R S G X Y n) :=
  extBaseChangeMap_injective_of_hasResolutionBy (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

/-- **`Ext` of smooth representations and localization.** Assume `ProPInvariantsExactStatement`,
let `p` be invertible in `R` and let `S` be a localization of `R`. If `X` has a resolution
`P_{n+1} → ⋯ → P_0 → X → 0` by smooth representations free of finite rank on vectors fixed by
pro-`p` subgroups, then `S ⊗[R] Ext^n_G(X, Y) → Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` is bijective. -/
theorem smoothExtBaseChangeMap_bijective_of_hasResolutionBy
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (HasProPFreeFixedBasis p) (n + 1) X) :
    Function.Bijective (smoothExtBaseChangeMap.{max uS w} R S G X Y n) :=
  extBaseChangeMap_bijective_of_hasResolutionBy (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

/-- Under the hypotheses of `smoothExtBaseChangeMap_bijective_of_hasResolutionBy`, the
`S`-linear equivalence `S ⊗[R] Ext^n_G(X, Y) ≃ Ext^n_G(S ⊗[R] X, S ⊗[R] Y)` given by
`smoothExtBaseChangeMap`. -/
def smoothExtBaseChangeEquivOfHasResolutionBy
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (HasProPFreeFixedBasis p) (n + 1) X) :
    S ⊗[R] Abelian.Ext.{t} X Y n ≃ₗ[S]
      Abelian.Ext.{t'} ((smoothRepExtendScalars.{max uS w} R S G).obj X)
        ((smoothRepExtendScalars.{max uS w} R S G).obj Y) n :=
  extBaseChangeEquivOfHasResolutionBy (smoothRepExtendScalars.{max uS w} R S G)
    (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Y (Q := HasProPFreeFixedBasis p)
    (fun _ hQ => hQ.projective hP hR)
    (fun _ hQ => hQ.projective_smoothRepExtendScalars S hP hR)
    (fun Q hQ => (extBaseChangeMap_zero_bijective_iff (smoothRepExtendScalars.{max uS w} R S G)
      (smoothRepExtendScalars_isSemilinear.{max uS w} R S G) Q Y).2
      (smoothHomBaseChangeMap_bijective_of_hasProPFreeFixedBasis S M hQ Y)) n hX

@[simp]
theorem smoothExtBaseChangeEquivOfHasResolutionBy_apply
    (hP : ProPInvariantsExactStatement.{uG, uR, max uS w}) {p : ℕ} (hR : IsUnit (p : R))
    (n : ℕ) {X : SmoothRep.{uR, uG, max uS w} R G}
    (hX : HasResolutionBy (HasProPFreeFixedBasis p) (n + 1) X)
    (z : S ⊗[R] Abelian.Ext.{t} X Y n) :
    smoothExtBaseChangeEquivOfHasResolutionBy.{w} S M Y hP hR n hX z =
      smoothExtBaseChangeMap.{max uS w} R S G X Y n z :=
  rfl

end Ext

end Localization

end HyperextScalarExtension

end Langlands.Cohomology
