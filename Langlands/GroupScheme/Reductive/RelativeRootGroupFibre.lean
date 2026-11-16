import Langlands.GroupScheme.Reductive.LocalRootGroupTorusCoordinate

/-! # Field-fibre root parametrizations of actual relative dynamic root groups -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace Langlands.GroupScheme.LocalRootGroup

open LocalSplitCell Corepresented

variable {R : Type u} [CommRing R] {G : GroupScheme (Spec (CommRingCat.of R))}
  [IsAffineHom G.X.hom] {I : Type u} [Fintype I]
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G) (mu nu : I → ℤ)

variable (K : Type u) [Field K] [Algebra R K]

/-- Compose a parametrization of the actual base-changed dynamic group with
its inclusion in the actual base-changed ambient group. -/
def fibreRootMap (Φ : Ga K ≅ UK i mu nu K) :
    Ga K ⟶ (GroupScheme.baseChange (algebraBaseMap R K)).obj G :=
  Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu) ≫ jZK i mu K

theorem fibreRootMap_eq (Φ : Ga K ≅ UK i mu nu K) :
    fibreRootMap i mu nu K Φ =
      Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (incl i mu nu) := by
  simp only [fibreRootMap, incl, jZK, Functor.map_comp]

private theorem weightPointAction_scalar {A : CommRingCat.{u}}
    {T : CommGroupScheme (Spec A)} (χ : characterLattice T)
    (Z : Over (Spec A)) (t : Z ⟶ T.X) (c : Γ(Z.left, ⊤)) :
    VectorGroup.weightPointAction χ Z t (VectorGroup.scalarPoint A Z c) =
      VectorGroup.scalarPoint A Z (VectorGroup.charValue χ Z t * c) := by
  apply VectorGroup.points_ext
  intro j
  rw [VectorGroup.coordinates_weightPointAction, Pi.smul_apply, smul_eq_mul,
    VectorGroup.coordinates_scalarPoint, VectorGroup.coordinates_scalarPoint]

variable (a : I → ℤ) (Φ : Ga K ≅ UK i mu nu K)
  (hΦ : ∀ (Z : Over (Spec (CommRingCat.of K)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (x : Z ⟶ (Ga K).X),
    (t ≫ (tK i mu K).hom.hom) *
        (x ≫ (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom) *
        (t ≫ (tK i mu K).hom.hom)⁻¹ =
      VectorGroup.weightPointAction (splitTorus.exponentCharacter _ I a) Z t x ≫
        (Φ.hom ≫ (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom)

include hΦ in
/-- The actual field-fibre inclusion has the expected root character on all tests. -/
theorem fibreRootMap_equivariant
    (Z : Over (Spec (CommRingCat.of K)))
    (t : Z ⟶ (splitTorus (Spec (CommRingCat.of K)) I).X) (c : Γ(Z.left, ⊤)) :
    (t ≫ (splitTorus.baseChangeHom (K := K) G I i).hom.hom) *
        rootPoint (fibreRootMap i mu nu K Φ) Z c *
        (t ≫ (splitTorus.baseChangeHom (K := K) G I i).hom.hom)⁻¹ =
      rootPoint (fibreRootMap i mu nu K Φ) Z
        (VectorGroup.charValue (splitTorus.exponentCharacter _ I a) Z t * c) := by
  have h := congrArg (fun f => f ≫ (jZK i mu K).hom.hom)
    (hΦ Z t (VectorGroup.scalarPoint (CommRingCat.of K) Z c))
  rw [weightPointAction_scalar] at h
  have ht : (tK i mu K).hom.hom ≫ (jZK i mu K).hom.hom =
      (splitTorus.baseChangeHom (K := K) G I i).hom.hom := by
    rw [← Grp.comp_hom_hom, tK_comp]
  simp only [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, ht] at h
  simpa only [fibreRootMap, rootPoint, Grp.comp_hom_hom, Category.assoc] using h

theorem isClosedSubgroup_fibreRootMap : IsClosedSubgroup (fibreRootMap i mu nu K Φ) := by
  have hU : IsClosedImmersion
      (((GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)).hom.hom.left) :=
    (Corepresented.isClosedSubgroup_unipotentHom (unipCochar i mu nu)).baseChange
      (algebraBaseMap R K)
  have hZ : IsClosedImmersion (jZK i mu K).hom.hom.left :=
    isClosedSubgroup_jZK i mu K
  change IsClosedImmersion (fibreRootMap i mu nu K Φ).hom.hom.left
  dsimp only [fibreRootMap, Grp.comp_hom_hom, Over.comp_left]
  infer_instance

include hΦ in
/-- The field-fibre parametrization represents exactly the root subgroup, not
merely a subgroup of it. -/
theorem isRootParametrization_fibreRootMap
    (ha0 : ∑ j, a j * mu j = 0) {d : ℕ} (hd : 0 < d)
    (had : ∑ j, a j * nu j = d) :
    IsRootParametrization (splitTorus.baseChangeHom (K := K) G I i) a
      (fibreRootMap i mu nu K Φ) := by
  let iK := splitTorus.baseChangeHom (K := K) G I i
  let Uj := (GroupScheme.baseChange (algebraBaseMap R K)).map (jU i mu nu)
  have hequiv := fibreRootMap_equivariant i mu nu K a Φ hΦ
  have hclosed := isClosedSubgroup_fibreRootMap i mu nu K Φ
  have : IsClosedImmersion (fibreRootMap i mu nu K Φ).hom.hom.left := hclosed
  refine ⟨⟨Over.mono_of_mono_left (fibreRootMap i mu nu K Φ).hom.hom,
    le_antisymm ?_ ?_⟩, hclosed, hequiv⟩
  · rintro Z g ⟨x, rfl⟩
    obtain ⟨c, rfl⟩ := (scalarPoint_bijective (CommRingCat.of K) Z).2 x
    exact rootPoint_mem_subgroup iK a hequiv c
  · intro Z g hg
    have hcent := subgroup_le_centralizer iK mu a ha0 Z hg
    obtain ⟨z, hz⟩ : ∃ z : Z ⟶ (ZK i mu K).X, z ≫ (jZK i mu K).hom.hom = g := by
      rw [← SubgroupFunctor.mem_range, (isRepresentedBy_jZK i mu K).2]
      exact hcent
    have hunip := subgroup_le_unipotent iK nu a hd had Z hg
    have hzunip : z ∈ (Dynamic.unipotent
        (CommGroupScheme.groupHom (splitTorus.exponentCocharacter _ I nu) ≫
          tK i mu K)).carrier Z := by
      rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup _
        (jZK i mu K) (isClosedSubgroup_jZK i mu K), SubgroupFunctor.mem_comap, hz,
        Category.assoc, tK_comp]
      exact hunip
    obtain ⟨y, hy⟩ : ∃ y : Z ⟶ (UK i mu nu K).X, y ≫ Uj.hom.hom = z := by
      rw [← SubgroupFunctor.mem_range, (isRepresentedBy_jUK i mu nu K).2]
      exact hzunip
    refine ⟨y ≫ Φ.inv.hom.hom, ?_⟩
    change (y ≫ Φ.inv.hom.hom) ≫ (fibreRootMap i mu nu K Φ).hom.hom = g
    rw [fibreRootMap, Grp.comp_hom_hom, Category.assoc,
      ← Category.assoc Φ.inv.hom.hom Φ.hom.hom.hom,
      ← Grp.comp_hom_hom, Iso.inv_hom_id, Grp.id_hom_hom, Category.id_comp,
      Grp.comp_hom_hom, ← Category.assoc, hy, hz]

variable {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- Field-fibre additive coordinates for a root isolated by `mu`. All
comparisons use the given field algebra structure and standard split-torus
coordinates. No locality or reducedness of the base ring is required. -/
theorem exists_rootFibreParametrization (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (α : J)
    (hmu0 : ∑ j, P.root α j * mu j = 0)
    (hmu : ∀ β : J, ∑ j, P.root β j * mu j = 0 →
      P.root β = P.root α ∨ P.root β = -P.root α) :
    ∃ Φ : Ga K ≅ UK i mu (P.coroot α) K,
      IsRootParametrization (splitTorus.baseChangeHom (K := K) G I i) (P.root α)
        (fibreRootMap i mu (P.coroot α) K Φ) := by
  have := hG.smooth
  have hGK := hG.isConnectedReductive_baseChange (algebraBaseMap R K)
  have hmaxK := splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise I G i hmax K
  have h2 : ∑ j, P.root α j * P.coroot α j = ((2 : ℕ) : ℤ) := by
    rw [← hP.pairing K, P.root_coroot_two]
    rfl
  have hroots : ∀ β ∈ roots (T := splitTorus.commGroupScheme _ I)
      (splitTorus.baseChangeHom (K := K) G I i),
      latticePairing _ β (splitTorus.exponentCocharacter _ I mu) = 0 →
        β = splitTorus.exponentCharacter _ I (P.root α) ∨
        β = -splitTorus.exponentCharacter _ I (P.root α) := by
    intro β hβ hβ0
    obtain ⟨m, rfl⟩ : ∃ m,
        splitTorus.exponentCharacter (Spec (CommRingCat.of K)) I m = β :=
      ⟨splitTorus.characterLatticeEquiv K I β, by
        rw [splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
          AddEquiv.symm_apply_apply]⟩
    obtain ⟨b, rfl⟩ := (hP.mem_roots_iff K m).1 hβ
    rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter] at hβ0
    rcases hmu b hβ0 with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by
        rw [h, splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm,
          splitTorus.exponentCharacter_eq_characterLatticeEquiv_symm, map_neg])
  obtain ⟨Φ, hΦ⟩ := exists_fibreIso i mu (P.coroot α) K hGK hmaxK
    (splitTorus.exponentCharacter _ I (P.root α))
    ((hP.mem_roots_iff K _).2 ⟨α, rfl⟩) hroots
    (by rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, hmu0])
    (by rw [splitTorus.latticePairing_exponentCharacter_exponentCocharacter, h2]; norm_num)
  exact ⟨Φ, isRootParametrization_fibreRootMap i mu (P.coroot α) K
    (P.root α) Φ hΦ hmu0 two_pos h2⟩

end Langlands.GroupScheme.LocalRootGroup
