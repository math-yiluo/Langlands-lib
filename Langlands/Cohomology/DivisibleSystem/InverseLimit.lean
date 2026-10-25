import Langlands.Cohomology.DivisibleSystem.InvariantLimit
import Langlands.Cohomology.InverseLimit.Statement

/-!
# Harris's inverse limit over `m` and Lemma 2.8

Harris 1999, §2, p.306: "The maps j : C_m^•(U(ẽ)_F̄) → C_{m'}^•(U(ẽ)_F̄), for m > m', are all
surjective by hypothesis. It thus follows from Fact 1 bis that the system of complexes
{C_m^•(U(ẽ)_F̄)} satisfies a Mittag-Leffler condition [EGA III, Chap. 0, Proposition 13.2.3],
hence that Lemma 2.8. For every q, there is a canonical isomorphism
H^q(lim C_m^•(U(ẽ)_F̄)) ≅ lim H_c^q(U(ẽ)_F̄, Z/ℓ^mZ)."

The first section shows that the canonical comparison `limit.post` from the homology of a limit
of complexes to the limit of the homologies is invertible if and only if it is after a functor
preserving homology and limits and reflecting isomorphisms
(`isIso_limit_post_homology_iff`). For an `ℓ`-divisible system of complexes,
`inverseLimit` is the limit of its tower and `inverseLimitHomologyComparison` is this
comparison. Given Worker 3's `FiniteCohomologyInverseLimitStatement`, it is an isomorphism for
systems of `ℤ`-graded complexes of modules or of representations with finite cohomology
(`isIso_inverseLimitHomologyComparison_of_finite`, `isIso_inverseLimitHomologyComparison_rep`);
the surjectivity of the transition maps holds for every `ℓ`-divisible system.

The last section specializes this to Harris's complexes: `quotientInvariantsInverseLimit` is the
inverse limit of the system `quotientInvariantsLimit` (our `C_m^•`), and
`quotientInvariantsInverseLimitComparison` composes `inverseLimitHomologyComparison` with the
inverse limit of the maps induced on cohomology by the comparison (2.6). Under the hypotheses of
`quasiIso_quotientInvariantsLimitToRepExtend` at every level,
`FiniteCohomologyInverseLimitStatement` and finiteness of the cohomology of `K`, it is an
isomorphism in every degree
(`isIso_quotientInvariantsInverseLimitComparison`), our rendering of Lemma 2.8.
-/

noncomputable section

namespace Langlands.Cohomology

open CategoryTheory CategoryTheory.Limits Opposite

universe w uR uG u v u' v'

section HomologyLimit

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] {ι : Type*} (c : ComplexShape ι)

/-- For a functor `F` preserving homology, the natural isomorphism between the homology of the
image of a complex under `F` and the image of its homology. -/
def mapHomologicalComplexHomologyIso (q : ι) :
    F.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor D c q ≅
      HomologicalComplex.homologyFunctor C c q ⋙ F :=
  NatIso.ofComponents (fun K => (K.sc q).mapHomologyIso F)
    (fun φ => ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C c q).map φ) F)

variable {J : Type*} [Category J] [HasLimitsOfShape J C] [HasLimitsOfShape J D]
  [PreservesLimitsOfShape J F] [F.ReflectsIsomorphisms]

/-- The canonical comparison from the homology of a limit of complexes to the limit of the
homologies is invertible if and only if the corresponding comparison after a functor `F` is,
for `F` preserving homology and limits of shape `J` and reflecting isomorphisms. -/
theorem isIso_limit_post_homology_iff (K : J ⥤ HomologicalComplex C c) (q : ι) :
    IsIso (limit.post K (HomologicalComplex.homologyFunctor C c q)) ↔
      IsIso (limit.post (K ⋙ F.mapHomologicalComplex c)
        (HomologicalComplex.homologyFunctor D c q)) := by
  set Hq := HomologicalComplex.homologyFunctor C c q
  set Hq' := HomologicalComplex.homologyFunctor D c q
  set F' := F.mapHomologicalComplex c
  set e := mapHomologicalComplexHomologyIso F c q
  have h₁ : F.map (limit.post K Hq) ≫ limit.post (K ⋙ Hq) F = limit.post K (Hq ⋙ F) :=
    limit.post_post K Hq F
  have h₂ : Hq'.map (limit.post K F') ≫ limit.post (K ⋙ F') Hq' = limit.post K (F' ⋙ Hq') :=
    limit.post_post K F' Hq'
  have h₃ : limit.post K (F' ⋙ Hq') ≫ limMap (Functor.whiskerLeft K e.hom) =
      e.hom.app (limit K) ≫ limit.post K (Hq ⋙ F) := by
    ext j
    simp only [Category.assoc, limMap_π, Functor.whiskerLeft_app, limit.post_π_assoc]
    rw [limit.post_π]
    exact e.hom.naturality (limit.π K j)
  have : IsIso (limit.post (K ⋙ Hq) F) := inferInstance
  have : IsIso (Hq'.map (limit.post K F')) := inferInstance
  calc IsIso (limit.post K Hq) ↔ IsIso (F.map (limit.post K Hq)) :=
        (isIso_iff_of_reflects_iso _ F).symm
    _ ↔ IsIso (limit.post K (Hq ⋙ F)) := by rw [← h₁, isIso_comp_right_iff]
    _ ↔ IsIso (e.hom.app (limit K) ≫ limit.post K (Hq ⋙ F)) := (isIso_comp_left_iff _ _).symm
    _ ↔ IsIso (limit.post K (F' ⋙ Hq')) := by rw [← h₃, isIso_comp_right_iff]
    _ ↔ IsIso (limit.post (K ⋙ F') Hq') := by rw [← h₂, isIso_comp_left_iff]

end HomologyLimit

section RepFinite

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G]

/-- Finiteness of the underlying type of a representation is invariant under isomorphism. -/
lemma finite_of_rep_iso {X Y : Rep.{w} k G} (e : X ≅ Y) (h : Finite X) : Finite Y :=
  have : Finite ((forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj X) := h
  Finite.of_equiv _ ((forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).mapIso e).toLinearEquiv.toEquiv

/-- A zero representation has finite underlying type. -/
lemma finite_of_rep_isZero {X : Rep.{w} k G} (h : IsZero X) : Finite X :=
  have : Subsingleton ((forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).obj X) :=
    ModuleCat.isZero_iff_subsingleton.1 ((forget₂ (Rep.{w} k G) (ModuleCat.{w} k)).map_isZero h)
  Finite.of_subsingleton

/-- If an `ℕ`-graded complex of representations has finite cohomology in every degree, so does
its extension by zero to `ℤ`. -/
lemma finite_homology_extend_embeddingUpNat (X : CochainComplex (Rep.{w} k G) ℕ)
    (h : ∀ n, Finite (X.homology n)) (q : ℤ) :
    Finite ((X.extend ComplexShape.embeddingUpNat).homology q) := by
  rcases q with n | n
  · exact finite_of_rep_iso (X.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).symm
      (h n)
  · refine finite_of_rep_isZero
      ((X.extend_exactAt ComplexShape.embeddingUpNat _ fun j hj => ?_).isZero_homology)
    simp only [ComplexShape.embeddingUpNat_f] at hj
    omega

end RepFinite

namespace DivisibleSystem

section InverseLimit

variable {C : Type u} [Category.{v} C] [Abelian C] {ℓ : ℕ}

/-- Every transition map of the tower of an `ℓ`-divisible system is an epimorphism. -/
lemma epi_tower_map (T : DivisibleSystem C ℓ) {i j : ℕᵒᵖ} (f : i ⟶ j) : Epi (T.tower.map f) :=
  (Subsingleton.elim (homOfLE (leOfHom f.unop)).op f) ▸ T.epi_projection (leOfHom f.unop)

variable {ι : Type*} {c : ComplexShape ι}

/-- For an `ℓ`-divisible system of complexes, the transition maps are epimorphisms in every
degree. -/
lemma epi_tower_map_f (T : DivisibleSystem (HomologicalComplex C c) ℓ) {i j : ℕᵒᵖ} (f : i ⟶ j)
    (q : ι) : Epi ((T.tower.map f).f q) := by
  have := T.epi_tower_map f
  infer_instance

variable [HasLimitsOfShape ℕᵒᵖ C]

/-- The inverse limit over `m` of an `ℓ`-divisible system, the limit of its tower. -/
abbrev inverseLimit (T : DivisibleSystem C ℓ) : C := limit T.tower

/-- For an `ℓ`-divisible system of complexes, the canonical comparison from the homology of the
inverse limit to the inverse limit of the homologies (Harris, Lemma 2.8). -/
def inverseLimitHomologyComparison (T : DivisibleSystem (HomologicalComplex C c) ℓ) (q : ι) :
    T.inverseLimit.homology q ⟶ limit (T.tower ⋙ HomologicalComplex.homologyFunctor C c q) :=
  limit.post T.tower (HomologicalComplex.homologyFunctor C c q)

@[reassoc (attr := simp)]
lemma inverseLimitHomologyComparison_π (T : DivisibleSystem (HomologicalComplex C c) ℓ) (q : ι)
    (m : ℕᵒᵖ) :
    T.inverseLimitHomologyComparison q ≫ limit.π _ m =
      HomologicalComplex.homologyMap (limit.π T.tower m) q :=
  limit.post_π _ _ _

end InverseLimit

section Modules

variable {R : Type u} [Ring R] {ℓ : ℕ}

/-- Given `FiniteCohomologyInverseLimitStatement`, for an `ℓ`-divisible system of `ℤ`-graded
complexes of `R`-modules with finite cohomology, the comparison
`inverseLimitHomologyComparison` is an isomorphism. -/
theorem isIso_inverseLimitHomologyComparison_of_finite
    (hS : FiniteCohomologyInverseLimitStatement.{u, v} R)
    (T : DivisibleSystem (CochainComplex (ModuleCat.{v} R) ℤ) ℓ)
    (hfin : ∀ m q, Finite ((T.obj m).homology q)) (q : ℤ) :
    IsIso (T.inverseLimitHomologyComparison q) :=
  hS T.tower (fun _ _ f q => (ModuleCat.epi_iff_surjective _).1 (T.epi_tower_map_f f q))
    (fun i q => hfin (unop i) q) q

end Modules

section Rep

variable {k : Type u} [CommRing k] {G : Type v} [Monoid G] {ℓ : ℕ}

/-- Given `FiniteCohomologyInverseLimitStatement` for the coefficient ring, for an `ℓ`-divisible
system of `ℤ`-graded complexes of representations with finite cohomology, the comparison
`inverseLimitHomologyComparison` is an isomorphism (of representations). -/
theorem isIso_inverseLimitHomologyComparison_rep
    (hS : FiniteCohomologyInverseLimitStatement.{u, w} k)
    (T : DivisibleSystem (CochainComplex (Rep.{w} k G) ℤ) ℓ)
    (hfin : ∀ m q, Finite ((T.obj m).homology q)) (q : ℤ) :
    IsIso (T.inverseLimitHomologyComparison q) := by
  let F := forget₂ (Rep.{w} k G) (ModuleCat.{w} k)
  have : PreservesLimitsOfSize.{0, 0} F := preservesSmallestLimits_of_preservesLimits F
  refine (isIso_limit_post_homology_iff F (ComplexShape.up ℤ) T.tower q).2 ?_
  refine hS (T.tower ⋙ F.mapHomologicalComplex _) (fun _ _ f q => ?_) (fun i q => ?_) q
  · have := T.epi_tower_map_f f q
    exact (ModuleCat.epi_iff_surjective _).1 (F.map_epi ((T.tower.map f).f q))
  · have : Finite (F.obj ((T.tower.obj i).sc q).homology) := hfin (unop i) q
    exact Finite.of_equiv _
      ((((T.tower.obj i).sc q).mapHomologyIso F).toLinearEquiv.toEquiv.symm)

end Rep

section Harris

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G] [TopologicalSpace G] {ℓ : ℕ}
  (N : ℕ) (K : DivisibleSystem (CochainComplex (SmoothRep.{uR, uG, max w uR uG} R G) ℕ) ℓ)
  {ι : Type uG} [Preorder ι] (H : ι → Subgroup G) (hH : Antitone H) [∀ i, (H i).Normal]
  [∀ i, (H i).FiniteIndex] [∀ i, Fintype (G ⧸ H i)] [∀ i, DecidableEq (G ⧸ H i)]
  (hK : ∀ i {m' m : ℕ} (h : m' ≤ m) (q : ℕ),
    Epi ((smoothQuotientInvariants R (H i)).map ((K.projection h).f q)))
  (hk : ∀ {i j : ι} (hij : i ≤ j), IsUnit (Nat.card (quotientProjection (hH hij)).ker : R))
  [IsFiltered ι]

/-- Our rendering of Harris's `lim C_m^•`: the inverse limit over `m` of
`quotientInvariantsLimit`. -/
abbrev quotientInvariantsInverseLimit : CochainComplex (Rep.{max w uR uG} R G) ℤ :=
  (quotientInvariantsLimit.{w, uR, uG} N K H hH hK hk).inverseLimit

/-- Our rendering of the map of Harris's Lemma 2.8: the comparison
`inverseLimitHomologyComparison` from the cohomology of `quotientInvariantsInverseLimit` to the
inverse limit of the cohomologies of the `C_m^•`, followed by the inverse limit of the maps
induced on cohomology by the comparison (2.6), `quotientInvariantsLimitToRepExtend`. -/
def quotientInvariantsInverseLimitComparison (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (q : ℤ) :
    (quotientInvariantsInverseLimit.{w, uR, uG} N K H hH hK hk).homology q ⟶
      limit (K.toRepComplexes.extendSystem.tower ⋙
        HomologicalComplex.homologyFunctor (Rep.{max w uR uG} R G) (ComplexShape.up ℤ) q) :=
  (quotientInvariantsLimit.{w, uR, uG} N K H hH hK hk).inverseLimitHomologyComparison q ≫
    limMap (Functor.whiskerRight
      (quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower
      (HomologicalComplex.homologyFunctor (Rep.{max w uR uG} R G) (ComplexShape.up ℤ) q))

variable [IsTopologicalGroup G]

/-- Given `ProPInvariantSubcomplexStatement` and `FiniteCohomologyInverseLimitStatement`, if every
`H i` is a normal pro-`p` subgroup with `p` invertible in `R` acting trivially on the cohomology
at every level, and the cohomology of `K` is finite at every level and in every degree, then the
comparison of Lemma 2.8 is an isomorphism in every degree. -/
theorem isIso_quotientInvariantsInverseLimitComparison
    (hS : ProPInvariantSubcomplexStatement.{uG, uR, max w uR uG})
    (hS' : FiniteCohomologyInverseLimitStatement.{uR, max w uR uG} R) {p : ℕ}
    (hP : ∀ i, IsProPSubgroup p (H i)) (hR : IsUnit (p : R))
    (hN : ∀ m q, N ≤ q → IsZero ((K.obj m).X q))
    (htriv : ∀ m i q (h : H i), ((K.toRepComplexes.obj m).homology q).ρ h = LinearMap.id)
    (hfin : ∀ m n, Finite ((K.toRepComplexes.obj m).homology n)) (q : ℤ) :
    IsIso (quotientInvariantsInverseLimitComparison.{w, uR, uG} N K H hH hK hk hN q) := by
  have hq : ∀ m : ℕᵒᵖ,
      QuasiIso ((quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower.app m) :=
    fun m => quasiIso_quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hS hP hR hN
      (unop m) (htriv (unop m))
  have hT : ∀ m q,
      Finite (((quotientInvariantsLimit.{w, uR, uG} N K H hH hK hk).obj m).homology q) :=
    fun m q => by
      have := hq (op m)
      exact finite_of_rep_iso (isoOfQuasiIsoAt
          ((quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower.app (op m))
          q).symm
        (finite_homology_extend_embeddingUpNat (K.toRepComplexes.obj m) (hfin m) q)
  have : IsIso ((quotientInvariantsLimit.{w, uR, uG} N K H hH hK hk).inverseLimitHomologyComparison
      q) := isIso_inverseLimitHomologyComparison_rep hS' _ hT q
  have : ∀ m, IsIso ((Functor.whiskerRight
      (quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower
      (HomologicalComplex.homologyFunctor (Rep.{max w uR uG} R G) (ComplexShape.up ℤ) q)).app m) :=
    fun m => by
      have := hq m
      change IsIso (HomologicalComplex.homologyMap _ q)
      infer_instance
  have : IsIso (Functor.whiskerRight
      (quotientInvariantsLimitToRepExtend.{w, uR, uG} N K H hH hK hk hN).tower
      (HomologicalComplex.homologyFunctor (Rep.{max w uR uG} R G) (ComplexShape.up ℤ) q)) :=
    NatIso.isIso_of_isIso_app _
  unfold quotientInvariantsInverseLimitComparison
  infer_instance

end Harris

end DivisibleSystem

end Langlands.Cohomology
