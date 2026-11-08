import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters
import Langlands.GroupScheme.Rational.RootSubgroupGaloisTransport

/-! # Coefficient transport of rational characters of arbitrary group schemes

For a group scheme `G` over `B`, a morphism `b : S ⟶ B` and an endomorphism `a` of `S`
over `B`, the existing transport of characters of `G_S` along `a` is additive on the
actual rational characters of `G_S`, is natural for homomorphisms defined over `B`, and
satisfies the identity and composition laws. Over a `k`-algebra `K` this gives the
representation of `Aut_k(K)` on `X^*(G_K)`, with `(σ χ)(σ x) = σ (χ x)` on `K`-points.
No commutativity of `G` is used.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)

/-- Character transport commutes with restriction along a homomorphism defined over the
original base. -/
theorem transportCharacter_naturality {H G : GroupScheme B} (f : H ⟶ G)
    (χ : (Over.pullback b).mapGrp.obj G ⟶ (Gm S).toGrp) :
    transportCharacter b a ha H ((Over.pullback b).mapGrp.map f ≫ χ) =
      (Over.pullback b).mapGrp.map f ≫ transportCharacter b a ha G χ := by
  apply hom_ext_points
  intro T y
  apply (Gm.pointsEquiv S T).injective
  rw [transportCharacter_points]
  change _ = Gm.pointsEquiv S T ((y ≫ ((Over.pullback b).mapGrp.map f).hom.hom) ≫
    (transportCharacter b a ha G χ).hom.hom)
  rw [transportCharacter_points, descentPoint_comp_baseChange, Category.assoc]
  rfl

namespace rationalCharacters

variable (G : GroupScheme B)

private theorem characterEval_transportRaw
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) (T : Over S)
    (y : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    characterEval (Additive.ofMul (transportCharacter b a ha G χ.toMul) :
        rationalCharacters ((GroupScheme.baseChange b).obj G)) T y =
      characterEval χ ((Over.map a).obj T) (descentPoint b a ha G T y) :=
  transportCharacter_points b a ha G χ.toMul T y

/-- Transport of the actual rational characters of `G_S` along `a`, as an additive map. -/
def transport : rationalCharacters ((GroupScheme.baseChange b).obj G) →+
    rationalCharacters ((GroupScheme.baseChange b).obj G) where
  toFun χ := Additive.ofMul (transportCharacter b a ha G χ.toMul)
  map_zero' := by
    apply ext_characterEval
    intro T y
    rw [characterEval_transportRaw, characterEval_zero, characterEval_zero]
  map_add' χ ψ := by
    apply ext_characterEval
    intro T y
    rw [characterEval_add, characterEval_transportRaw, characterEval_transportRaw,
      characterEval_transportRaw, characterEval_add]

theorem transport_toMul (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    (transport b a ha G χ).toMul = transportCharacter b a ha G χ.toMul := rfl

/-- The transported character evaluates the original character at the same point, seen with
the `S`-structure changed by `a`. -/
theorem characterEval_transport (χ : rationalCharacters ((GroupScheme.baseChange b).obj G))
    (T : Over S) (y : T ⟶ ((GroupScheme.baseChange b).obj G).X) :
    characterEval (transport b a ha G χ) T y =
      characterEval χ ((Over.map a).obj T) (descentPoint b a ha G T y) :=
  characterEval_transportRaw b a ha G χ T y

theorem transport_id (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    transport b (𝟙 S) (Category.id_comp b) G χ = χ :=
  congrArg Additive.ofMul (transportCharacter_id b G χ.toMul)

theorem transport_transport (c : S ⟶ S) (hc : c ≫ b = b)
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    transport b a ha G (transport b c hc G χ) =
      transport b (a ≫ c) (by rw [Category.assoc, hc, ha]) G χ :=
  congrArg Additive.ofMul (transportCharacter_comp b a ha G c hc χ.toMul)

theorem transport_of_eq_id (h : a = 𝟙 S)
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    transport b a ha G χ = χ := by
  subst h
  exact transport_id b G χ

theorem transport_transport_of_eq (c : S ⟶ S) (hc : c ≫ b = b) (d : S ⟶ S)
    (hd : d ≫ b = b) (h : a ≫ c = d)
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    transport b a ha G (transport b c hc G χ) = transport b d hd G χ := by
  subst h
  exact transport_transport b a ha G c hc χ

variable {G} in
/-- Transport commutes with restriction along a homomorphism defined over the original
base. -/
theorem characterRestrict_transport {H : GroupScheme B} (f : H ⟶ G)
    (χ : rationalCharacters ((GroupScheme.baseChange b).obj G)) :
    characterRestrict ((GroupScheme.baseChange b).map f) (transport b a ha G χ) =
      transport b a ha H (characterRestrict ((GroupScheme.baseChange b).map f) χ) :=
  congrArg Additive.ofMul (transportCharacter_naturality b a ha f χ.toMul).symm

end rationalCharacters

end Transport

section Galois

variable (k K : Type u) [CommRing k] [CommRing K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

namespace rationalCharacters

/-- The action of `Aut_k(K)` on the actual rational characters `X^*(G_K)` of an arbitrary
group scheme `G` over `k`: `σ` acts by transport along `Spec σ`. -/
def galoisRepresentation : Representation ℤ (K ≃ₐ[k] K)
    (rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) where
  toFun σ := (transport (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G).toIntLinearMap
  map_one' := LinearMap.ext fun χ =>
    transport_of_eq_id (algebraBaseMap k K) _ _ G (galoisBaseMap_one k K) χ
  map_mul' σ τ := LinearMap.ext fun χ =>
    (transport_transport_of_eq (algebraBaseMap k K) _ _ G _ _ _ _
      (galoisBaseMap_mul k K σ τ).symm χ).symm

theorem galoisRepresentation_apply (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    galoisRepresentation k K G σ χ =
      transport (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) G χ :=
  rfl

/-- On points, `σ χ` evaluates `χ` at the same point of `G`, seen with the `K`-structure
changed by `Spec σ`. -/
theorem characterEval_galoisRepresentation (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (U : Over (Spec (CommRingCat.of K)))
    (y : U ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X) :
    characterEval (galoisRepresentation k K G σ χ) U y =
      characterEval χ ((Over.map (galoisBaseMap k K σ)).obj U)
        (descentPoint (algebraBaseMap k K) (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
          G U y) := by
  rw [galoisRepresentation_apply]
  exact characterEval_transport (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G χ U y

variable {G} in
/-- Restriction along a homomorphism defined over `k` is equivariant. -/
theorem characterRestrict_galoisRepresentation {H : GroupScheme (Spec (CommRingCat.of k))}
    (f : H ⟶ G) (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    characterRestrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f)
        (galoisRepresentation k K G σ χ) =
      galoisRepresentation k K H σ
        (characterRestrict ((GroupScheme.baseChange (algebraBaseMap k K)).map f) χ) :=
  characterRestrict_transport (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) f χ

/-- For a commutative group scheme the action is the existing action on the character
lattice. -/
theorem equivCharacterLattice_galoisRepresentation
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters
      ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp) :
    equivCharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (galoisRepresentation k K T.toGrp σ χ) =
      characterLattice.galoisRepresentation k K T σ
        (equivCharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ) :=
  rfl

theorem galoisRepresentation_self_inv (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    galoisRepresentation k K G σ (galoisRepresentation k K G σ⁻¹ χ) = χ :=
  Representation.self_inv_apply _ σ χ

end rationalCharacters

end Galois

section Field

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

private theorem units_ΓSpecIso_spec_map {R R' : CommRingCat.{u}} (f : R ⟶ R')
    (z : (Γ(Spec R, ⊤))ˣ) :
    Units.map (Scheme.ΓSpecIso R').hom.hom.toMonoidHom
        (Units.map (Spec.map f).appTop.hom.toMonoidHom z) =
      Units.map f.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso R).hom.hom.toMonoidHom z) := by
  apply Units.ext
  change ((Spec.map f).appTop ≫ (Scheme.ΓSpecIso R').hom) _ =
    ((Scheme.ΓSpecIso R).hom ≫ f) _
  rw [Scheme.ΓSpecIso_naturality]

/-- Evaluation of a simultaneously transported rational character and `K`-point is the
coefficient automorphism applied to the original value. -/
theorem rationalCharacterEval_galoisRepresentation (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (x : rationalPoints (baseChanged k K G)) :
    rationalCharacterEval (rationalCharacters.galoisRepresentation k K G σ χ)
        (rationalConjugate k K G σ x) =
      Units.map σ.toMonoidHom (rationalCharacterEval χ x) := by
  have h : characterEval (rationalCharacters.galoisRepresentation k K G σ χ)
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (rationalConjugate k K G σ x) =
      Units.map (galoisIdentityTestIso k K σ).hom.left.appTop.hom.toMonoidHom
        (characterEval χ (Over.mk (𝟙 (Spec (CommRingCat.of K)))) x) := by
    rw [rationalCharacters.characterEval_galoisRepresentation,
      descentPoint_rationalConjugate, characterEval_naturality]
  exact (congrArg (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom) h).trans
    (units_ΓSpecIso_spec_map (CommRingCat.ofHom σ.toRingHom) _)

/-- If `σ χ' = χ`, then evaluating `χ` at a transported point applies `σ` to the value of
`χ'`. -/
theorem rationalCharacterEval_rationalConjugate_of_eq (σ : K ≃ₐ[k] K)
    (χ χ' : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (h : rationalCharacters.galoisRepresentation k K G σ χ' = χ)
    (x : rationalPoints (baseChanged k K G)) :
    rationalCharacterEval χ (rationalConjugate k K G σ x) =
      Units.map σ.toMonoidHom (rationalCharacterEval χ' x) := by
  subst h
  exact rationalCharacterEval_galoisRepresentation k K G σ χ' x

/-- Inverse form: evaluating `χ` at a transported point applies the coefficient automorphism to
the value of the inversely transported character. -/
theorem rationalCharacterEval_rationalConjugate (σ : K ≃ₐ[k] K)
    (χ : rationalCharacters ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (x : rationalPoints (baseChanged k K G)) :
    rationalCharacterEval χ (rationalConjugate k K G σ x) =
      Units.map σ.toMonoidHom
        (rationalCharacterEval (rationalCharacters.galoisRepresentation k K G σ⁻¹ χ) x) :=
  rationalCharacterEval_rationalConjugate_of_eq k K G σ χ _
    (rationalCharacters.galoisRepresentation_self_inv k K G σ χ) x

end Field

end Langlands.GroupScheme
