# The divisor sequence of a relative effective Cartier divisor and its twists

The module `Langlands.AlgebraicGeometry.Picard.RelativeDivisorFibreSequence` is an internal helper
for the proof of `ProjectiveRelativeDivisorFibreHilbertStatement`. Its content is general
homological algebra of the divisor sequence. The tensor products in this module are the explicit
sheafified tensor `Langlands.Scheme.Modules.tensorObj` of the Library, written `⊗ₑ` below.

## Declarations

Let `i : E ⟶ X` be a closed immersion. `K = kernelModule i` is its ideal module and
`ι = kernelModuleι i`, `π = unitToPushforwardUnit i`.

- `divisorSequence i`: the short complex `K ⟶ 𝒪_X ⟶ i_* 𝒪_E` with maps `ι`, `π`.
- `shortExact_divisorSequence_map i b`: for any `b : X' ⟶ X` such that `b^*(ι)` is a
  monomorphism, the pulled-back sequence is short exact. Its exactness comes from the Library's
  `pullbackKernelIsKernel` (proof module of `RelativeEffectiveDivisorBaseChangeStatement`). The
  epimorphism comes from `epi_unitToPushforwardUnit` together with preservation of epimorphisms
  by the left adjoint `b^*`.
- `mono_pullback_fst_kernelModuleι i f h hK`: if `K` is invertible and `i ≫ f` is flat, then
  `ι` stays a monomorphism after pullback along `pullback.fst f h`, for every `h : T ⟶ S`.
  The Library lemma `mono_pullback_snd_kernelModuleι` covers `pullback.snd h f`. This lemma
  transports it along `pullbackSymmetry`, whose pullback functor preserves finite limits (flat;
  `flatPullbackExact`).
- `twistObj L M n`: `M ⊗ₑ L ⊗ₑ ⋯ ⊗ₑ L` (`n` factors `L`, associated to the right).
  `twistObjMapIso` is its functoriality in isomorphisms `M ≅ M'`.
- `twistSeq L hL S n`: the short complex `S` with the functor `tensorBy L` (Library
  `CoherentEulerSequence`) applied `n` times. Here `L` is locally free of rank one.
  `shortExact_twistSeq` shows that it is short exact if `S` is, by `shortExact_tensorBy`.
  `twistSeq_X₁`, `twistSeq_X₂` and `twistSeq_X₃` identify its terms with `twistObj L S.Xᵢ n`.
- `projectionStep L hL j G : (j_* G) ⊗ₑ L ≅ j_* (G ⊗ₑ j^* L)`. This is the Library
  `lineBundleProjectionIso` conjugated by `tensorComm`. `twistPushforwardIso` iterates it:
  `twistObj L (j_* G) n ≅ j_* (twistObj (j^* L) G n)`.
- `finrank_relativeGlobalSections_X₃ g hS h₁`: let `g : Y ⟶ Spec K` with `K` a field, and let `S`
  be a short exact sequence of modules on `Y`. Assume `H¹(Y, S.X₁) = 0` and that `H⁰(Y, S.X₂)` is
  finite dimensional. Then `h⁰(S.X₃) = h⁰(S.X₂) − h⁰(S.X₁)` (as integers; `h⁰` is the
  `K`-dimension of `relativeGlobalSections g`). By the Library
  `DerivedPlus.shortExact_map_of_isZero_rightDerived_one`, global sections send `S` to a short
  exact sequence of `K`-vector spaces. The equality is then rank–nullity.

The proofs use only the axioms `propext`, `Classical.choice` and `Quot.sound`.
