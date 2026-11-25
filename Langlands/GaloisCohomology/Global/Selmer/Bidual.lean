import Langlands.GaloisCohomology.Global.Selmer.SelmerGroup
import Langlands.GaloisCohomology.Global.EulerCharacteristic.Multiplicative
import Langlands.Cohomology.Profinite.Cup.Graded

/-!
# The double dual of a family of local conditions

Let `K` be a number field, `S` a finite set of finite places containing the places above `N ≥ 1`,
`M` a finite smooth `G_S`-module killed by `N`, `M' = Hom(M, μ_N)` and `M'' = Hom(M', μ_N)`.
Evaluation `M → M''` is an isomorphism (`toBidualIso`). For a family `L` of local conditions for
`M`, the dual of the dual family `L^⊥⊥ = (L.dual N).dual N`, a family for `M''`, is `L` carried
over to `M''` by this isomorphism (`LocalConditions.dual_dual`), and so its Selmer group is the
image of `Sel_L(M)` (`LocalConditions.selmerGroup_dual_dual`).

The point is the sign rule for the local pairings: for `x ∈ H¹(K_v, M)` and `y ∈ H¹(K_v, M')`,
`⟨y, x⟩_{M'} = -⟨x, y⟩_M` (`ptLocalPairing_dual_toDualDual` of
`Langlands.GaloisCohomology.CompactSupport.NineTerm`), by the graded commutativity of the cup product
(`coeffMap_braiding_cup`) and the identity `ev_{M'}(f ⊗ ev(m)) = f(m) = ev_M(m ⊗ f)`.
A family of local conditions is carried along an isomorphism of modules by
`LocalConditions.map`, and Selmer groups follow (`LocalConditions.selmerGroup_map`).
-/

namespace Langlands.GaloisCohomology

open CategoryTheory MonoidalCategory Langlands.ProfiniteCohomology Langlands.Galois NumberField
  IsDedekindDomain PoitouTate

universe u

noncomputable section

section Orthogonal

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- If `P' (b, e a) = -P (a, b)` for an isomorphism `e : A ≃ C`, the right orthogonal for `P'` of
`Y ⊆ B` is the image under `e` of the left orthogonal for `P`. -/
theorem rightOrthogonal_eq_map_leftOrthogonal (P : A →+ B →+ QZ) (P' : B →+ C →+ QZ)
    (e : A ≃+ C) (h : ∀ a b, P' b (e a) = -P a b) (Y : AddSubgroup B) :
    rightOrthogonal P' Y = (leftOrthogonal P Y).map e.toAddMonoidHom := by
  ext c
  obtain ⟨a, rfl⟩ := e.surjective c
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply]
  refine forall₂_congr fun b _ => ?_
  rw [h, neg_eq_zero]
  rfl

end Orthogonal

section Bidual

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω) (N : ℕ) [NeZero N]
  (M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)) [IsSmoothRep M] [Finite M]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

/-- **`M ≅ M''`**: evaluation `M → Hom(Hom(M, μ_N), μ_N)` is an isomorphism when `N` kills `M` and
`S` contains the places above `N`. -/
def toBidualIso : M ≅ PoitouTate.dual N (PoitouTate.dual N M) :=
  repIsoOfBijective (toDualDual (dualizingModule K Ω S N) M)
    (bijective_toDualDual (nonempty_addEquiv_dualizingModule hS) hM)

omit [IsSmoothRep M] in
theorem toBidualIso_hom : (toBidualIso N M hS hM).hom = toDualDual (dualizingModule K Ω S N) M :=
  rfl

end Bidual

section Naturality

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} (ι : PlaceEmbeddings K Ω)

/-- Localization at a finite place commutes with maps of coefficients. -/
theorem localization_coeffMap {A B : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)}
    [IsSmoothRep A] [IsSmoothRep B] (f : A ⟶ B) (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : cohomology A n) :
    localization ι B v n (coeffMap f n x) =
      coeffMap ((Rep.resFunctor (localizationHom ι S v :
        Gal(AlgebraicClosure (v.adicCompletion K)/v.adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)).map f) n (localization ι A v n x) := by
  rw [localization_apply, localization_apply, map_coeffMap_hom_apply,
    ← ConcreteCategory.comp_apply, map_comp_coeffMap, Category.comp_id, Category.id_comp]

end Naturality

section BidualPairing

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

attribute [local instance 2000] IsSepClosure.isGalois

/-- `M'' = Hom(Hom(M, μ_N), μ_N)` is smooth. (A high priority keeps the instance search from
trying the instances for discrete or trivial actions first.) -/
instance (priority := high) isSmoothRep_dual_dual :
    IsSmoothRep (PoitouTate.dual N (PoitouTate.dual N M)) :=
  isSmoothRep_dual N (PoitouTate.dual N M)

/-- `M''` is smooth as a module of a local Galois group at a finite place. -/
instance isSmoothRep_localModule_dual_dual (v : HeightOneSpectrum (𝓞 K)) :
    IsSmoothRep (localModule ι (PoitouTate.dual N (PoitouTate.dual N M)) v) :=
  isSmoothRep_res _ _

/-- `M''` is smooth as a module of a local Galois group at an infinite place. -/
instance isSmoothRep_realLocalModule_dual_dual (w : InfinitePlace K) :
    IsSmoothRep (realLocalModule ι (PoitouTate.dual N (PoitouTate.dual N M)) w) :=
  isSmoothRep_res _ _

include hS hM in
/-- The sign rule at a place `v ∈ S`: `⟨y, x⟩_{M'} = -⟨x, y⟩_M`, `M` mapped to `M''`. -/
theorem localPairing_dual_toBidualIso (v : S) (x : cohomology (localModule ι M v) 1)
    (y : cohomology (localModule ι (PoitouTate.dual N M) v) 1) :
    localPairing ι N (PoitouTate.dual N M) v y
        (coeffAddEquiv ((Rep.resFunctor (localizationHom ι S v :
          Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)/
            (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) →*
              GaloisGroupUnramifiedOutside K Ω S)).mapIso (toBidualIso N M hS hM)) 1 x) =
      -localPairing ι N M v x y := by
  rw [localPairing_eq, localPairing_eq, coeffAddEquiv_apply, Functor.mapIso_hom, toBidualIso_hom]
  exact ptLocalPairing_dual_toDualDual (localFamily ι S) (dualizingModule K Ω S N) M
    (fun v => invariantAt ι S N v) v x y

include hS hM in
/-- The sign rule at a real place: `⟨y, x⟩_{M'} = -⟨x, y⟩_M`, `M` mapped to `M''`. -/
theorem realLocalPairing_dual_toBidualIso (w : {w : InfinitePlace K // w.IsReal})
    (x : cohomology (realLocalModule ι M w.1) 1)
    (y : cohomology (realLocalModule ι (PoitouTate.dual N M) w.1) 1) :
    realLocalPairing ι N (PoitouTate.dual N M) w y
        (coeffAddEquiv ((Rep.resFunctor (realLocalizationHom ι S w.1 :
          Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
            GaloisGroupUnramifiedOutside K Ω S)).mapIso (toBidualIso N M hS hM)) 1 x) =
      -realLocalPairing ι N M w x y := by
  rw [realLocalPairing_eq, realLocalPairing_eq, coeffAddEquiv_apply, Functor.mapIso_hom,
    toBidualIso_hom]
  exact ptLocalPairing_dual_toDualDual (realFamily ι S) (dualizingModule K Ω S N) M
    (fun w => realInvariantAt ι S N w.1) w x y

end BidualPairing

namespace LocalConditions

section Map

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {ι : PlaceEmbeddings K Ω}
  {M₁ M₂ : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M₁]
  [IsSmoothRep M₂]

attribute [local instance 2000] IsSepClosure.isGalois

/-- A family of local conditions carried along an isomorphism of modules: the images of the `L_v`
and `L_w` under the induced isomorphisms of local cohomology. -/
def map (e : M₁ ≅ M₂) (L : LocalConditions ι M₁) : LocalConditions ι M₂ where
  finite v := (L.finite v).map (coeffAddEquiv ((Rep.resFunctor (localizationHom ι S v :
    Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)/
      (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) →*
        GaloisGroupUnramifiedOutside K Ω S)).mapIso e) 1).toAddMonoidHom
  real w := (L.real w).map (coeffAddEquiv ((Rep.resFunctor (realLocalizationHom ι S w.1 :
    Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
      GaloisGroupUnramifiedOutside K Ω S)).mapIso e) 1).toAddMonoidHom

/-- **The Selmer group of the carried conditions** is the image of the Selmer group. -/
theorem selmerGroup_map (e : M₁ ≅ M₂) (L : LocalConditions ι M₁) :
    (L.map e).selmerGroup = L.selmerGroup.map (coeffAddEquiv e 1).toAddMonoidHom := by
  ext y
  obtain ⟨x, rfl⟩ := (coeffAddEquiv e 1).surjective y
  rw [AddSubgroup.mem_map_equiv, AddEquiv.symm_apply_apply, mem_selmerGroup, mem_selmerGroup]
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun w => ?_)
  · have h := localization_coeffMap ι e.hom (v : HeightOneSpectrum (𝓞 K)) 1 x
    rw [← coeffAddEquiv_apply] at h
    change _ ∈ AddSubgroup.map _ _ ↔ _
    rw [h, AddSubgroup.mem_map_equiv]
    exact Iff.of_eq (congrArg (· ∈ L.finite v) (AddEquiv.symm_apply_apply _ _))
  · have h := realLocalization_coeffMap ι e.hom w.1 1 x
    rw [← coeffAddEquiv_apply] at h
    change _ ∈ AddSubgroup.map _ _ ↔ _
    rw [h, AddSubgroup.mem_map_equiv]
    exact Iff.of_eq (congrArg (· ∈ L.real w) (AddEquiv.symm_apply_apply _ _))

end Map

section DualDual

variable {K Ω : Type u} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  {S : Set (HeightOneSpectrum (𝓞 K))} {ι : PlaceEmbeddings K Ω} {N : ℕ} [NeZero N]
  {M : Rep.{u} (ULift.{u} ℤ) (GaloisGroupUnramifiedOutside K Ω S)} [IsSmoothRep M] [Finite M]
  (hS : ∀ v : HeightOneSpectrum (𝓞 K), ((N : ℕ) : 𝓞 K) ∈ v.asIdeal → v ∈ S)
  (hM : ∀ m : M, N • m = 0)

attribute [local instance 2000] IsSepClosure.isGalois

include hS hM in
/-- **`(L^⊥)^⊥ = L`**: the dual of the dual family of conditions is the family `L` carried over to
`M'' = Hom(Hom(M, μ_N), μ_N)` by evaluation. -/
theorem dual_dual (L : LocalConditions ι M) :
    (L.dual N).dual N = L.map (toBidualIso N M hS hM) := by
  have := fun v : S => finite_cohomology_localModule ι M v 1
  have := fun v : S => finite_cohomology_localModule ι (PoitouTate.dual N M) v 1
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι M w 1 (by norm_num)
  have := fun w : {w : InfinitePlace K // w.IsReal} =>
    finite_cohomology_realLocalModule ι (PoitouTate.dual N M) w 1 (by norm_num)
  refine LocalConditions.ext (funext fun v => ?_) (funext fun w => ?_)
  · let e := coeffAddEquiv ((Rep.resFunctor (localizationHom ι S v :
      Gal(AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)/
        (v : HeightOneSpectrum (𝓞 K)).adicCompletion K) →*
          GaloisGroupUnramifiedOutside K Ω S)).mapIso (toBidualIso N M hS hM)) 1
    change rightOrthogonal (localPairing ι N (PoitouTate.dual N M) v)
      (rightOrthogonal (localPairing ι N M v) (L.finite v)) = _
    rw [rightOrthogonal_eq_map_leftOrthogonal (localPairing ι N M v)
      (localPairing ι N (PoitouTate.dual N M) v) e (localPairing_dual_toBidualIso hS hM v),
      leftOrthogonal_rightOrthogonal _ (bijective_localPairing ι N M hS hM v)
        (bijective_localPairing_flip ι N M hS hM v)]
    rfl
  · let e := coeffAddEquiv ((Rep.resFunctor (realLocalizationHom ι S w.1 :
      Gal(AlgebraicClosure w.1.Completion/w.1.Completion) →*
        GaloisGroupUnramifiedOutside K Ω S)).mapIso (toBidualIso N M hS hM)) 1
    change rightOrthogonal (realLocalPairing ι N (PoitouTate.dual N M) w)
      (rightOrthogonal (realLocalPairing ι N M w) (L.real w)) = _
    rw [rightOrthogonal_eq_map_leftOrthogonal (realLocalPairing ι N M w)
      (realLocalPairing ι N (PoitouTate.dual N M) w) e (realLocalPairing_dual_toBidualIso hS hM w),
      leftOrthogonal_rightOrthogonal _ (bijective_realLocalPairing ι N M hS hM w)
        (bijective_realLocalPairing_flip ι N M hS hM w)]
    rfl

include hS hM in
/-- The Selmer group of `(L^⊥)^⊥` is the image of `Sel_L(M)` in `H¹(G_S, M'')`. -/
theorem selmerGroup_dual_dual (L : LocalConditions ι M) :
    ((L.dual N).dual N).selmerGroup =
      L.selmerGroup.map (coeffAddEquiv (toBidualIso N M hS hM) 1).toAddMonoidHom := by
  rw [dual_dual hS hM, selmerGroup_map]

end DualDual

end LocalConditions

end

end Langlands.GaloisCohomology
