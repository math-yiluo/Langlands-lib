# Maps to the dual through forgotten Picard classes

Lean module: `Langlands.AlgebraicGeometry.Picard.MumfordMapPicardClass`, namespace
`Langlands.AbelianScheme.MumfordPicardClass`. Author: Worker 195.

Let `A` be an abelian scheme over `S` with Rosati prerequisites `P` and dual data `W`, so that
`W.dual P` is the Library's constructed dual, with underlying scheme `dualScheme A W.hasDual`.
A `T`-point of the dual classifies a rigidified family of line bundles on `T ×_S A`. This
module compares points of the dual through the ordinary Picard class of that family,
forgetting the rigidification. The comparison is injective and turns the group law into
addition. Over a field, it computes the classes of the Mumford maps
`φ_L : a ↦ t_a^*L ⊗ L⁻¹` and of `g ≫ φ_L ≫ g^∨`. The module serves the proof of the
staged statement `Langlands.AbelianScheme.Rosati.MumfordEulerDegreeStatement`, where these
facts show that `n • φ_L + f ≫ φ_L ≫ f^∨ = φ_{f^*L ⊗ L^n}`.

## Provenance

This is an internal formalization device; `pointClass` transcribes no source definition. It
implements the standard identities of Milne, *Abelian Varieties* (1986 article, author
revision January 2, 2022; registered source `milne-abelian-varieties-1986-author-2022`),
Remark 6.8, p.10, where `φ_L(a)` is the class of `t_a^*L ⊗ L⁻¹`. The identities
`φ_{L ⊗ N} = φ_L + φ_N` and `φ_{g^*L} = g^∨ ∘ φ_L ∘ g` follow directly from that formula; Milne
does not state them there in this form. Here they appear as identities of classes of the
Mumford family `m^*L ⊗ p₁^*L⁻¹ ⊗ p₂^*L⁻¹` on `A ×_S A`.

## Declarations

### `pointClass P A W p` (definition)

For a test object `T` over `S` and `p : T ⟶ dualScheme A W.hasDual`, the element
`RigidifiedLineBundle.forgetClasses … T (dualPointClass P.stability A W.hasDual p).val` of the
Picard group of `T ×_S A` (`(relativeSpace A.X.hom).obj T`). In words: the isomorphism class
of the underlying line bundle of the family that `p` classifies.

### General lemmas (any base `S`)

- `pointClass_injective`: `pointClass` is injective on `T`-points. Proof: the Library's
  `dualPointClass_injective`, `Subtype.ext`, and `RigidifiedLineBundle.forgetClasses_injective`
  (rigidified classes are determined by their underlying classes, because the rigidification
  section has a retraction).
- `pointClass_mul`: `pointClass (p * q) = pointClass p + pointClass q`, where `p * q` is the
  product for the group law of `W.dual P`. Proof: `dualAbelianSchemePointMulEquiv` is
  multiplicative. The product of classes is the class of the rigidified tensor product, whose
  underlying line bundle is the ordinary tensor product, and `RelativePicard.classOf_tensor`
  applies.
- `pointClass_one`, `pointClass_pow`: the unit point has class `0`
  (`FieldMumfordFiniteLocus.forgetClasses_trivialClass`), and
  `pointClass (p ^ n) = n • pointClass p`, by induction.
- `pointClass_comp`: for `h : T ⟶ U`,
  `pointClass (h ≫ p) = Group.pullback ((relativeSpace A.X.hom).map h) (pointClass p)`.
  Proof: `dualPointClass_comp` and `FieldMumfordFiniteLocus.forgetClasses_classesPullback`.
- `pointClass_dualSchemeMap`: for an endomorphism `g` of `A`,
  `pointClass (p ≫ dualSchemeMap homPicardZeroPullback g _ _) =
  Group.pullback ((homFamilySpaceMap g).app T) (pointClass p)`, i.e. pullback along
  `(t, a) ↦ (t, g a)`. Proof: `dualPointClass_dualSchemeMap`, and
  `RigidifiedLineBundle.pullbackForgetIso` on representatives.
- `pointClass_mumfordSchemeMapOfLineBundle`: the class of the Mumford map
  `mumfordSchemeMapOfLineBundle P.preservation A L B evaluationB M evaluation P.square W.hasDual`
  is the class of the underlying bundle of `mumfordFamilyOfLineBundle`. Proof:
  `RigidifiedLineBundle.classifyingMap_eq_iff` with `mumfordSchemeMapOfLineBundlePullbackIso`.
- `hom_add_eq_mul`, `hom_nsmul_eq_pow`: for homomorphisms `a b : A ⟶ B` of abelian schemes,
  the underlying morphism of `a + b` is the pointwise product of those of `a` and `b`, and that
  of `n • a` is the `n`-th power (definitional, and induction on `n`).

### Over a field

Let `A` be an abelian scheme over `Spec k`. Write `m`, `p₁`, `p₂ : A ×_S A → A` for the Mumford
addition `mumfordAddition A` and the two projections.

- `classOf_mumfordFamily P k A`: the class of the underlying bundle of
  `mumfordFamilyOfLineBundle P.preservation A L B evaluationB M evaluation` is
  `m^*[L] - p₁^*[L] - p₂^*[L]`. Proof: `mumfordFamilyOfLineBundle_forget` gives the bundle
  `m^*(L ⊗ π^*B) ⊗ p₁^*M ⊗ p₂^*M`. `[B] = 0` because line bundles on `Spec k` are trivial
  (`fieldLineBundleTriviality`). `[M] = -[L ⊗ π^*B] = -[L]` by `evaluation`. Finally, pullback
  is a group homomorphism (`Group.pullback_lineBundle_classOf`).
- `homFamilySpaceMap_comp_relativeSpace_map`: the composite of `(t, a) ↦ (t, g a)` with
  `(t, a) ↦ (g t, a)` is the product map `mumfordProductMap g` of `AmpleMumfordTransport`
  (`pullback.hom_ext`).
- `pullback_twice`: if `r : A ×_S A → A` satisfies `mumfordProductMap g ≫ r = r ≫ hom g`,
  pulling a class back along `r` and then along the two maps above equals pulling it back
  along `hom g` and then `r`. Proof: functoriality of `Group.pullback` (`Group.pullback_comp`).
- `pointClass_comp_mumford_comp_dual`: for an endomorphism `g`, the class of
  `(groupHom g).hom.hom ≫ φ_L ≫ dualSchemeMap homPicardZeroPullback g _ _` is
  `m^*[g^*L] - p₁^*[g^*L] - p₂^*[g^*L]`, the class formula for `g^*L`. Proof:
  `pointClass_dualSchemeMap`, `pointClass_comp`, the formula for `L`, then `pullback_twice`
  with `mumfordProductMap_addition`, `mumfordProductMap_fst` and `mumfordProductMap_snd`
  (`g` commutes with addition and the projections).

The proofs in the field section raise `synthInstance.maxHeartbeats` because typeclass
synthesis on the Library's Picard groups is slow.
