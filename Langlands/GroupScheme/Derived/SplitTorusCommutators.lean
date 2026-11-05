import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Torus.CommutatorEnd
import Langlands.GroupScheme.Torus.SplitMultiplication
import Langlands.GroupScheme.Torus.MaximalAmbient
import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Cocharacters, reflection commutators and closed subgroups -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme

section Cocharacters

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Cocharacters whose composite with the ambient homomorphism lands in the
given subgroup functor on every test scheme. -/
def cocharactersLandingIn (i : T.toGrp ⟶ G) (F : SubgroupFunctor G) :
    Submodule ℤ (cocharacterLattice T) where
  carrier := {ν | ∀ (U : Over S) (z : U ⟶ (Gm S).X),
    z ≫ (CommGroupScheme.groupHom ν ≫ i).hom.hom ∈ F.carrier U}
  zero_mem' := by
    intro U z
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zero, MonObj.one_comp]
    exact (F.carrier U).one_mem
  add_mem' := by
    intro ν eta hν heta U z
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    exact (F.carrier U).mul_mem (hν U z) (heta U z)
  smul_mem' := by
    intro m ν hν U z
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul, GrpObj.zpow_comp]
    exact (F.carrier U).zpow_mem (hν U z) m

/-- Coordinate cocharacters generate a split torus on all test schemes. -/
theorem IsSplitTorus.range_le_of_cocharacters
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (F : SubgroupFunctor G)
    (h : cocharactersLandingIn i F = ⊤) :
    SubgroupFunctor.range i ≤ F := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let _ : Fintype I := Fintype.ofFinite I
  let E : T ≅ splitTorus.commGroupScheme S I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  have he :
      (∑ a : I, (E.hom ≫ splitTorus.proj S I a) ≫
        (splitTorus.single S I a ≫ E.inv)) = 𝟙 T := by
    calc
      _ = E.hom ≫ (∑ a : I, splitTorus.proj S I a ≫
          splitTorus.single S I a) ≫ E.inv := by
        simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc]
      _ = _ := by rw [splitTorus.sum_proj_comp_single]; simp
  rintro U x ⟨t, rfl⟩
  change U ⟶ T.X at t
  have ht : t = ∏ a : I,
      (t ≫ (CommGroupScheme.groupHom (E.hom ≫ splitTorus.proj S I a)).hom.hom) ≫
        (CommGroupScheme.groupHom (splitTorus.single S I a ≫ E.inv)).hom.hom := by
    have ht := comp_groupHom_sum t Finset.univ (fun a : I =>
      (E.hom ≫ splitTorus.proj S I a) ≫ (splitTorus.single S I a ≫ E.inv))
    rw [he] at ht
    have hid : (CommGroupScheme.groupHom (𝟙 T)).hom.hom = 𝟙 T.X := rfl
    rw [hid, Category.comp_id] at ht
    refine ht.trans (Finset.prod_congr rfl fun a _ => ?_)
    exact comp_groupHom_comp t (E.hom ≫ splitTorus.proj S I a)
      (splitTorus.single S I a ≫ E.inv)
  let φ : (U ⟶ T.X) →* (U ⟶ G.X) := ((yonedaGrp.map i).app (op U)).hom
  change t ∈ (F.carrier U).comap φ
  rw [ht]
  apply ((F.carrier U).comap φ).prod_mem
  intro a _
  have hν : splitTorus.single S I a ≫ E.inv ∈ cocharactersLandingIn i F := by
    rw [h]
    exact Submodule.mem_top
  exact hν U (t ≫ (CommGroupScheme.groupHom (E.hom ≫ splitTorus.proj S I a)).hom.hom)

/-- Commutators with a normalizer point produce cocharacters in the subgroup. -/
theorem cocharacter_torusCommutatorEnd_mem
    (i : T.toGrp ⟶ G) {F : SubgroupFunctor G} (hF : F.ContainsCommutators)
    (n : normalizerPoints i) (ν : cocharacterLattice T) :
    ν ≫ torusCommutatorEnd i n ∈ cocharactersLandingIn i F := by
  intro U z
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_comp,
    Category.assoc, comp_torusCommutatorEnd]
  exact hF U _ _

end Cocharacters

section Field

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- The cocharacters landing in a closed subgroup form a saturated submodule:
nonzero integer multiples can be removed by fpqc descent along multiplication
on the multiplicative group. -/
theorem mem_cocharactersLandingIn_of_zsmul_mem
    (i : T.toGrp ⟶ G) {j : H ⟶ G} (hj : IsClosedSubgroup j)
    {ν : cocharacterLattice T} {m : ℤ} (hm : m ≠ 0)
    (hν : m • ν ∈ cocharactersLandingIn i (SubgroupFunctor.range j)) :
    ν ∈ cocharactersLandingIn i (SubgroupFunctor.range j) := by
  let q := multiplication (Gm (Spec (CommRingCat.of k))).toGrp m
  obtain ⟨hFlat, hSurj⟩ :=
    (isSplitTorus_gm (S := Spec (CommRingCat.of k))).flat_and_surjective_multiplication hm
  let : Flat q.hom.hom.left := hFlat
  let : Surjective q.hom.hom.left := hSurj
  let : IsAffineHom (Gm (Spec (CommRingCat.of k))).toGrp.X.hom :=
    (isSplitTorus_gm (S := Spec (CommRingCat.of k))).isAffineHom
  let : IsAffine (Gm (Spec (CommRingCat.of k))).X.left :=
    isAffine_of_isAffineHom (Gm (Spec (CommRingCat.of k))).toGrp.X.hom
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hf : (CommGroupScheme.groupHom ν ≫ i).hom.hom ∈
      (SubgroupFunctor.range j).carrier (Gm (Spec (CommRingCat.of k))).X := by
    apply SubgroupFunctor.mem_range_of_comp_mem_range j q.hom.hom
    rw [Grp.comp_hom_hom, ← Category.assoc]
    dsimp only [q]
    rw [multiplication_hom, GrpObj.zpow_comp, Category.id_comp]
    have h := hν (Gm (Spec (CommRingCat.of k))).X (𝟙 _)
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_zsmul,
      Category.id_comp] at h
    exact h
  intro U z
  exact (SubgroupFunctor.range j).comp_mem z hf

/-- An actual reflection of a root datum negates its corresponding coroot. -/
theorem IsRootDatumOf.cocharacterAut_coroot
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) {J : Type*}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) (a : J) (σ : T ≅ T)
    (hσ : characterAut σ = P.reflection a) :
    cocharacterAut σ (P.coroot a) = -P.coroot a := by
  apply P.flip.toPerfPair.injective
  apply LinearMap.ext
  intro χ
  change P.toLinearMap χ (cocharacterAut σ (P.coroot a)) =
    P.toLinearMap χ (-P.coroot a)
  rw [hP.1]
  have h := latticePairing_characterAut_cocharacterAut σ (P.reflection a χ) (P.coroot a)
  rw [hσ, P.reflection_same] at h
  rw [h, RootPairing.reflection_apply]
  simp only [map_sub, LinearMap.sub_apply, LinearMap.smul_apply, map_zsmul, smul_eq_mul,
    LinearMap.map_neg]
  rw [← hP.1, P.root_coroot_two]
  change P.toLinearMap χ (P.coroot a) - P.toLinearMap χ (P.coroot a) * 2 =
    -P.toLinearMap χ (P.coroot a)
  ring

/-- Every coroot of an actual split-torus root datum lands in each closed
subgroup containing all commutators. -/
theorem IsRootDatumOf.coroot_mem_cocharactersLandingIn
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    {J : Type*} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i P) {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcomm : (SubgroupFunctor.range j).ContainsCommutators) (a : J) :
    P.coroot a ∈ cocharactersLandingIn i (SubgroupFunctor.range j) := by
  obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 a
  let n' : normalizerPoints i := ⟨n, σ, hn⟩
  have hn' : normalizingAut i n' = σ :=
    (isNormalizingPoint_normalizingAut i n').unique i hn
  have hinv : P.coroot a ≫ (normalizingAut i n').hom = -P.coroot a := by
    rw [hn']
    exact hP.cocharacterAut_coroot i a σ hσ
  have he : P.coroot a ≫ torusCommutatorEnd i n' = (-2 : ℤ) • P.coroot a := by
    rw [torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id, hinv]
    module
  apply mem_cocharactersLandingIn_of_zsmul_mem i hj (m := (-2 : ℤ)) (by norm_num)
  rw [← he]
  exact cocharacter_torusCommutatorEnd_mem i hcomm n' (P.coroot a)

end Field

end Langlands.GroupScheme
