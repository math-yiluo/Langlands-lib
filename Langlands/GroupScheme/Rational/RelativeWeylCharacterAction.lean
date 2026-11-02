import Langlands.GroupScheme.Rational.RelativeRoots

/-! # The faithful relative Weyl action on all characters of a split torus -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section CharacterSeparation

variable {S : Scheme.{u}} {T H : CommGroupScheme S}

/-- Characters of a split torus separate homomorphisms into it. -/
theorem IsSplitTorus.hom_ext_characters (hT : IsSplitTorus T.toGrp) {f g : H ⟶ T}
    (h : ∀ χ : characterLattice T, f ≫ χ = g ≫ χ) : f = g := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme S I :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let : Fintype I := Fintype.ofFinite I
  have : IsIso eC.hom := eC.isIso_hom
  apply (cancel_mono eC.hom).1
  calc
    f ≫ eC.hom = (f ≫ eC.hom) ≫
        ∑ c, splitTorus.proj S I c ≫ splitTorus.single S I c := by
      rw [splitTorus.sum_proj_comp_single, Category.comp_id]
    _ = (g ≫ eC.hom) ≫
        ∑ c, splitTorus.proj S I c ≫ splitTorus.single S I c := by
      simp only [Preadditive.comp_sum, ← Category.assoc]
      exact Finset.sum_congr rfl fun c _ =>
        congrArg (fun a => a ≫ splitTorus.single S I c) (h (eC.hom ≫ splitTorus.proj S I c))
    _ = g ≫ eC.hom := by
      rw [splitTorus.sum_proj_comp_single, Category.comp_id]

/-- An automorphism of a split torus acting trivially on its characters is the identity. -/
theorem IsSplitTorus.characterAut_eq_one_iff (hT : IsSplitTorus T.toGrp) (σ : T ≅ T) :
    characterAut σ = 1 ↔ σ = Iso.refl T := by
  constructor
  · intro h
    have hinv : σ.inv = 𝟙 T := hT.hom_ext_characters fun χ => by
      have hχ := congrArg (fun a : characterLattice T ≃ₗ[ℤ] characterLattice T => a χ) h
      change σ.inv ≫ χ = χ at hχ
      simpa only [Category.id_comp] using hχ
    apply Iso.ext
    rw [← Category.comp_id σ.hom, ← hinv, Iso.hom_inv_id]
    rfl
  · rintro rfl
    apply LinearEquiv.ext
    intro χ
    exact Category.id_comp χ

end CharacterSeparation

section NormalizerKernel

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- On a split torus, the kernel of the normalizer action on all characters is
exactly the subgroup of centralizing points. -/
theorem IsSplitTorus.weylAction_eq_one_iff (hT : IsSplitTorus T.toGrp)
    (n : normalizerPoints i) :
    weylAction i n = 1 ↔ (n : Over.mk (𝟙 S) ⟶ G.X) ∈ centralizerPoints i := by
  constructor
  · intro hn
    have hσ := (hT.characterAut_eq_one_iff (normalizingAut i n)).mp hn
    have h := isNormalizingPoint_normalizingAut i n
    rw [hσ] at h
    exact h
  · intro hn
    apply LinearEquiv.ext
    intro χ
    rw [weylAction_eq i hn χ]
    exact Category.id_comp χ

/-- The full-character Weyl action has the expected centralizer kernel over any base. -/
theorem IsSplitTorus.weylAction_ker (hT : IsSplitTorus T.toGrp) :
    (weylAction i).ker = (centralizerPoints i).subgroupOf (normalizerPoints i) :=
  Subgroup.ext fun n => hT.weylAction_eq_one_iff i n

end NormalizerKernel

section RelativeQuotient

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]

/-- The relative Weyl quotient acts on the entire character lattice. -/
def relativeWeylCharacterAction :
    relativeWeylGroup i →* (characterLattice T ≃ₗ[ℤ] characterLattice T) :=
  QuotientGroup.lift _ (weylAction i) (centralizerPoints_subgroupOf_le_ker i)

@[simp]
theorem relativeWeylCharacterAction_mk (n : normalizerPoints i) :
    relativeWeylCharacterAction i (QuotientGroup.mk n) = weylAction i n :=
  rfl

/-- For a split torus the action of `N(k)/Z(k)` on all characters is faithful.
No reductivity or maximality assumption is used. -/
theorem IsSplitTorus.relativeWeylCharacterAction_injective (hT : IsSplitTorus T.toGrp) :
    Function.Injective (relativeWeylCharacterAction i) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact (hT.weylAction_eq_one_iff i n).mp hq

end RelativeQuotient

end Langlands.GroupScheme
