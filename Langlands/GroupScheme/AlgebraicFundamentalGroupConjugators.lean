import Langlands.GroupScheme.AlgebraicFundamentalGroupStatement
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots

/-! # Geometric conjugators between presentations of the algebraic fundamental group -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

namespace Choice

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
variable (E : Type u) [Field E] [Algebra k E]

/-- Postcomposition with a torus homomorphism on geometric cocharacter lattices. -/
def latticeMap {a b : Choice k G}
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus) :
    a.lattice E →ₗ[ℤ] b.lattice E :=
  (AddMonoidHom.mk' (fun ν => ν ≫ e)
    (fun _ _ => Preadditive.add_comp _ _ _ _ _ _)).toIntLinearMap

@[simp] theorem latticeMap_apply {a b : Choice k G}
    (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ⟶
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus) (ν : a.lattice E) :
    latticeMap E e ν = ν ≫ e := rfl

/-- The identity point conjugates a maximal torus to itself through the identity. -/
theorem isConjugationComparison_refl (a : Choice k G) :
    a.IsConjugationComparison E a 1 (Iso.refl _) := by
  unfold IsConjugationComparison
  rw [innerIso_one_hom, Category.comp_id]
  exact (Category.id_comp _).symm

variable {E}

/-- Conjugators compose: first `g`, then `h`. -/
theorem IsConjugationComparison.trans {a b c : Choice k G}
    {g h : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    {e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj c.torus}
    (h₁ : a.IsConjugationComparison E b g e) (h₂ : b.IsConjugationComparison E c h e') :
    a.IsConjugationComparison E c (h * g) (e ≪≫ e') := by
  unfold IsConjugationComparison at *
  rw [innerIso_mul_hom, ← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  rfl

/-- The inverse point conjugates back through the inverse isomorphism. -/
theorem IsConjugationComparison.symm {a b : Choice k G}
    {g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) :
    b.IsConjugationComparison E a g⁻¹ e.symm := by
  unfold IsConjugationComparison at *
  have key : CommGroupScheme.groupHom e.symm.hom ≫ CommGroupScheme.groupHom e.hom = 𝟙 _ := by
    change CommGroupScheme.groupHom (e.inv ≫ e.hom) = _
    rw [Iso.inv_hom_id]
    rfl
  rw [innerIso_inv_hom, Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc, key]
  exact (Category.id_comp _).symm

/-- Two conjugators between the same presentations differ by a normalizing point. -/
theorem IsConjugationComparison.isNormalizingPoint {a b : Choice k G}
    {g g' : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) (h' : a.IsConjugationComparison E b g' e') :
    IsNormalizingPoint ((GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion)
      (g' * g⁻¹) (e.symm ≪≫ e') :=
  h.symm.trans h'

/-- Canonical Galois descent transport carries a conjugator to a conjugator, and the
transported torus isomorphism intertwines the Galois actions on cocharacters. -/
theorem IsConjugationComparison.exists_galois {a b : Choice k G}
    {g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) (σ : E ≃ₐ[k] E) :
    ∃ (g' : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g' e' ∧
        ∀ ν : a.lattice E,
          cocharacterLattice.galoisRepresentation k E b.torus σ (ν ≫ e.hom) =
            cocharacterLattice.galoisRepresentation k E a.torus σ ν ≫ e'.hom := by
  have hα := galoisBaseMap_over k E σ
  let e' := (CommGroupScheme.descentBaseChangeIso _ _ hα a.torus).symm ≪≫
    (CommGroupScheme.baseChange (galoisBaseMap k E σ)).mapIso e ≪≫
      CommGroupScheme.descentBaseChangeIso _ _ hα b.torus
  have he' : CommGroupScheme.groupHom e'.hom =
      (descentBaseChangeIso _ _ hα a.torus.toGrp).inv ≫
        (GroupScheme.baseChange (galoisBaseMap k E σ)).map (CommGroupScheme.groupHom e.hom) ≫
          (descentBaseChangeIso _ _ hα b.torus.toGrp).hom := rfl
  have hc : HomConjugate ((GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion)
      (CommGroupScheme.groupHom e.hom ≫
        (GroupScheme.baseChange (algebraBaseMap k E)).map b.inclusion) := ⟨g, h⟩
  obtain ⟨g', hg'⟩ := ((hc.baseChange (galoisBaseMap k E σ)).postcomp
    (descentBaseChangeIso _ _ hα G).hom).precomp
      (descentBaseChangeIso _ _ hα a.torus.toGrp).inv
  refine ⟨g', e', ?_, fun ν => ?_⟩
  · unfold IsConjugationComparison
    simp only [Category.assoc, Functor.map_comp] at hg'
    rw [reassoc_of% (descentBaseChangeIso_naturality _ _ hα a.inclusion),
      Iso.inv_hom_id_assoc, descentBaseChangeIso_naturality _ _ hα b.inclusion] at hg'
    rw [hg', he']
    simp only [Category.assoc]
  · apply Additive.toMul.injective
    change transportCocharacter _ _ hα b.torus.toGrp
        (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom e.hom) =
      transportCocharacter _ _ hα a.torus.toGrp (CommGroupScheme.groupHom ν) ≫
        CommGroupScheme.groupHom e'.hom
    rw [he']
    simp only [transportCocharacter, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- If conjugators from `b` to itself act trivially modulo the coroot image of `b`,
then two conjugators from `a` to `b` induce the same class of every cocharacter. -/
theorem projection_comp_eq_of_conjugation {a b : Choice k G}
    (hC : ∀ (n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (σ : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      b.IsConjugationComparison E b n σ → ∀ ξ : b.lattice E, ξ ≫ σ.hom - ξ ∈ b.corootImage E)
    {g g' : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) (h' : a.IsConjugationComparison E b g' e')
    (ν : a.lattice E) :
    b.projection E (ν ≫ e'.hom) = b.projection E (ν ≫ e.hom) := by
  have hmem := hC _ _ (h.symm.trans h') (ν ≫ e.hom)
  have hcomp : (ν ≫ e.hom) ≫ (e.symm ≪≫ e').hom = ν ≫ e'.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hcomp] at hmem
  exact (Submodule.Quotient.eq _).mpr hmem

variable (E)

/-- Two linear maps out of `X_*(T_a)/X_*(T_a,sc)` agree once they agree on representatives. -/
theorem atChoice_hom_ext {a b : Choice k G} {f f' : a.atChoice E →ₗ[ℤ] b.atChoice E}
    (h : ∀ ν : a.lattice E, f (a.projection E ν) = f' (a.projection E ν)) : f = f' :=
  Submodule.linearMap_qext _ (LinearMap.ext h)

/-- A conjugator preserving the coroot images induces a canonical comparison. -/
theorem isCanonicalComparison_mapQ {a b : Choice k G}
    {g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e)
    (hB : a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom)) :
    a.IsCanonicalComparison E b
      ((a.corootImage E).mapQ (b.corootImage E) (latticeMap E e.hom) hB) :=
  ⟨g, e, h, fun _ => rfl⟩

/-- The chosen comparison is computed by every conjugator, as soon as one conjugator
preserves the coroot images and conjugators from `b` to itself act trivially. -/
theorem comparison_projection_of_conjugation {a b : Choice k G}
    (hB : ∀ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g e →
        a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom))
    (hC : ∀ (n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (σ : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      b.IsConjugationComparison E b n σ → ∀ ξ : b.lattice E, ξ ≫ σ.hom - ξ ∈ b.corootImage E)
    {g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G)}
    {e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
      (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus}
    (h : a.IsConjugationComparison E b g e) (ν : a.lattice E) :
    a.comparison E b (a.projection E ν) = b.projection E (ν ≫ e.hom) := by
  obtain ⟨g₀, e₀, h₀, hf⟩ :=
    a.comparison_spec E b ⟨_, isCanonicalComparison_mapQ E h (hB g e h)⟩
  rw [hf]
  exact projection_comp_eq_of_conjugation hC h h₀ ν

/-- **Assembly.** Existence of conjugators, preservation of coroot images, triviality of
self-conjugators modulo coroot images, and Galois transport of conjugators give all clauses
of the canonical comparison statement for fixed `k`, `E` and `G`. -/
theorem comparison_of_conjugators
    (hA : ∀ a b : Choice k G,
      ∃ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
        (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
          (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
        a.IsConjugationComparison E b g e)
    (hB : ∀ (a b : Choice k G)
      (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g e →
        a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom))
    (hC : ∀ (b : Choice k G)
      (n : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (σ : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      b.IsConjugationComparison E b n σ → ∀ ξ : b.lattice E, ξ ≫ σ.hom - ξ ∈ b.corootImage E)
    (hD : ∀ (a b : Choice k G)
      (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g e → ∀ σ : E ≃ₐ[k] E,
        ∃ (g' : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
          (e' : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
            (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
          a.IsConjugationComparison E b g' e' ∧
            ∀ ν : a.lattice E,
              cocharacterLattice.galoisRepresentation k E b.torus σ (ν ≫ e.hom) =
                cocharacterLattice.galoisRepresentation k E a.torus σ ν ≫ e'.hom) :
    (∀ a b : Choice k G,
      (∃! f, a.IsCanonicalComparison E b f) ∧
      a.IsCanonicalComparison E b (a.comparison E b) ∧
      Function.Bijective (a.comparison E b) ∧
      (∀ (σ : E ≃ₐ[k] E) (x : a.atChoice E),
        a.comparison E b (a.galoisRepresentation E σ x) =
          b.galoisRepresentation E σ (a.comparison E b x)) ∧
      (∀ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
        (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
          (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
        a.IsConjugationComparison E b g e →
        ∀ ν : a.lattice E,
          a.comparison E b (a.projection E ν) = b.projection E (ν ≫ e.hom))) ∧
    (∀ a : Choice k G, a.comparison E a = LinearMap.id) ∧
    (∀ a b c : Choice k G,
      (b.comparison E c).comp (a.comparison E b) = a.comparison E c) := by
  have happly : ∀ (a b : Choice k G)
      (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g e → ∀ ν : a.lattice E,
        a.comparison E b (a.projection E ν) = b.projection E (ν ≫ e.hom) :=
    fun a b _ _ h ν => comparison_projection_of_conjugation E (hB a b) (hC b) h ν
  have hid : ∀ a : Choice k G, a.comparison E a = LinearMap.id := by
    intro a
    refine atChoice_hom_ext E fun ν => ?_
    rw [happly a a 1 (Iso.refl _) (isConjugationComparison_refl E a) ν]
    simp only [Iso.refl_hom, Category.comp_id, LinearMap.id_apply]
  have hcomp : ∀ a b c : Choice k G,
      (b.comparison E c).comp (a.comparison E b) = a.comparison E c := by
    intro a b c
    obtain ⟨g, e, h⟩ := hA a b
    obtain ⟨g', e', h'⟩ := hA b c
    refine atChoice_hom_ext E fun ν => ?_
    rw [LinearMap.comp_apply, happly a b g e h ν, happly b c g' e' h' (ν ≫ e.hom),
      happly a c _ _ (h.trans h') ν]
    simp only [Iso.trans_hom, Category.assoc]
  refine ⟨fun a b => ?_, hid, hcomp⟩
  obtain ⟨g, e, h⟩ := hA a b
  have hcan : a.IsCanonicalComparison E b (a.comparison E b) :=
    a.comparison_spec E b ⟨_, isCanonicalComparison_mapQ E h (hB a b g e h)⟩
  refine ⟨⟨a.comparison E b, hcan, fun f hf => ?_⟩, hcan, ?_, ?_, happly a b⟩
  · obtain ⟨g₁, e₁, h₁, hf₁⟩ := hf
    refine atChoice_hom_ext E fun ν => ?_
    rw [hf₁, happly a b g₁ e₁ h₁ ν]
  · constructor
    · refine Function.LeftInverse.injective (g := b.comparison E a) fun x => ?_
      rw [← LinearMap.comp_apply, hcomp, hid, LinearMap.id_apply]
    · refine Function.RightInverse.surjective (g := b.comparison E a) fun x => ?_
      rw [← LinearMap.comp_apply, hcomp, hid, LinearMap.id_apply]
  · intro σ x
    obtain ⟨ν, rfl⟩ := (a.corootImage E).mkQ_surjective x
    obtain ⟨g', e', h', hgal⟩ := hD a b g e h σ
    change a.comparison E b (a.galoisRepresentation E σ (a.projection E ν)) =
      b.galoisRepresentation E σ (a.comparison E b (a.projection E ν))
    rw [galoisRepresentation_projection, happly a b g' e' h', happly a b g e h ν,
      galoisRepresentation_projection, hgal]

end Choice

end Langlands.GroupScheme.AlgebraicFundamentalGroup
