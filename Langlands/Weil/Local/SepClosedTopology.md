# Topology and unramified characters of the local Weil group of a separable closure

Let `K` be a nonarchimedean local field in Mathlib's sense, of either
characteristic, and `Ω` a separable closure of `K`. The module
`Langlands.Weil.Local.SepClosedTopology` proves the facts about the Weil group
`localWeilGroup K Ω` of [Assembly.md](Assembly.md) that the generic
finite-image and unramified-reduction theorems
(`Langlands.Weil.finiteImageExtension`, `Langlands.Weil.unramifiedReduction`)
consume. They are the general-field forms of the corresponding p-adic results of
[AssemblyProof.md](AssemblyProof.md), and their proofs use only the
pullback interface of [Pullback.md](../Pullback.md) and the residue map of
the separable closure.

The theorems carry the instance arguments `[IsSepClosure K Ω] [IsSepClosed Ω]`;
the second is `IsSepClosure.sep_closed K`, which a caller supplies with
`have : IsSepClosed Ω := IsSepClosure.sep_closed K`.

## The absolute Galois group

- `absoluteGalois_nonarchimedean`: for any field extension `Ω/K` the Krull
  topology of `Ω ≃ₐ[K] Ω` has the fixing subgroups of finite intermediate fields
  as a basis of open subgroups at the identity (Mathlib's
  `krullTopology_mem_nhds_one_iff`), so it is a `NonarchimedeanGroup`.
- `absoluteGalois_t2Space` and `absoluteGalois_compactSpace`: for a separable
  closure the group is Hausdorff (`krullTopology_t2`, the extension being
  algebraic) and compact (Mathlib's instance for Galois extensions; a separable
  closure is Galois by `IsSepClosure.isGalois`).

## The Weil group

- `localResidueDegree_isOpenMap`: the residue degree
  `localResidueDegree K Ω : Gal(Ω/K) → Ẑ` is the composite of the residue map
  `LocalGalois.SepClosed.absoluteResidueHom K Ω`, which is open by
  `LocalGalois.SepClosed.isOpenMap_absoluteResidueHom`, and the homeomorphism
  `Galois.FiniteField.profiniteEquivalence`, so it is open.
- `localProjection_denseRange`: the image of `localProjection K Ω` is the
  preimage of the image of `ℤ → Ẑ` (`Weil.projection_range`). That image is dense
  in the profinite completion (`ProfiniteGrp.ProfiniteCompletion.denseRange`),
  and the preimage of a dense set under an open map is dense.
- `localInertia_isOpen`: the degree-zero subgroup is open by
  `Weil.topologyProperties`.
- `localInertia_isCompact`: the degree-zero subgroup is the image of the kernel of
  the residue degree under the continuous inclusion `Weil.inertiaInclusion`
  (`Weil.inertiaInclusion_range`). That kernel is closed in the compact group
  `Ω ≃ₐ[K] Ω`, hence compact.
- `localWeilGroup_nonarchimedean`: the Weil group is a subgroup of
  `Gal(Ω/K) × ℤ` with `ℤ` discrete; both factors are nonarchimedean, and the
  Library instance `Langlands.subgroupNonarchimedean` passes this to subgroups.
- `localProjection_mem_absoluteInertia`: a degree-zero Weil element projects into
  `LocalGalois.SepClosed.absoluteInertia K Ω`, because the residue degree of its
  projection is the image of its degree and the kernel of the residue degree is
  absolute inertia (`localResidueDegree_ker`).
- `localProjection_localInertiaInclusion` and `localInertiaInclusion_mem`: the
  inclusion `localInertiaInclusion K Ω` of absolute inertia is a section of the
  projection over absolute inertia and lands in degree zero (both by definition).

## Unramified characters

- `localUnramifiedCharacter_on_inertia` and
  `localUnramifiedCharacter_geometricFrobenius`: the character
  `localUnramifiedCharacter K Ω z` is trivial on degree zero and takes the value
  `z` at the chosen geometric Frobenius `localGeometricFrobenius K Ω`.
- `localUnramifiedCharacter_eq_of_on_inertia`: a homomorphism
  `χ : localWeilGroup K Ω →* ℂˣ` trivial on degree zero equals
  `localUnramifiedCharacter K Ω (χ (localGeometricFrobenius K Ω))`. For `g` of
  degree `n`, the element `g · Frob⁻ⁿ` has degree zero, so `χ g = χ(Frob)ⁿ`.
  This is the general-field form of the p-adic
  `Langlands.Weil.Local.localUnramifiedCharacterClassificationFor`
  ([CharacterNormProof.md](CharacterNormProof.md)), with the same proof.

These are internal lemmas about the Library's constructions. Their mathematical
content is the description of the Weil group in Guy Henniart, *Représentations du
groupe de Weil d'un corps local*, L'Enseignement Math. 26 (1980), §§2.1–2.2,
printed p. 158 (registered as `henniart-1980-weil-representations`): inertia is
an open subgroup, the map to the Galois group is continuous with dense image, and
an unramified representation is determined by its value at a Frobenius element.
