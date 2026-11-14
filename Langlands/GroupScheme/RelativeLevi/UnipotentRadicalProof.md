# Existence and uniqueness of relative unipotent radicals

Worker 637, with the radical uniqueness development by Worker 590.

`Langlands.GroupScheme.relativeUnipotentRadical.{u}` proves exactly the
published `Langlands.GroupScheme.RelativeUnipotentRadicalStatement.{u}`.
For every scheme `S`, reductive group scheme `G/S`, and relative parabolic
homomorphism `i : P → G`, it constructs a group scheme `U/S` and a homomorphism
`r : U → P` satisfying `IsRelativeUnipotentRadical r`. Thus `r` is closed,
`U/S` is smooth, its image is normal on every relative test scheme, and its
geometric fibres are the unipotent radicals of those of `P`. Every other
homomorphism with this certificate has the same subgroup functor range as `r`.
The universe and base scheme are arbitrary.

The proof installs affineness of `P/S` from the supplied relative parabolic
certificate. The published theorem `relativeParabolicEtaleLocalDynamic`
provides an etale cover of `S` on which the actual pullback of `i` represents
the dynamic parabolic of a local cocharacter.

`RelativeLevi.radicalOfEtaleDynamicCover`, supplied with the published
`dynamicRelativeLevi` theorem, then constructs an actual global relative
unipotent radical. Its implementation constructs local dynamic radicals,
proves equality of their ranges on scheme-theoretic overlaps, descends the
closed subgroup representatives, and glues smoothness, normality and the
geometric-fibre radical condition. The final proof extracts the resulting
group, inclusion and certificate.

For any other relative radical, the proof applies
`RelativeLevi.radical_range_eq_of_etale_dynamicCover` to the same cover and
dynamic presentations, again supplying `dynamicRelativeLevi`. This compares
the actual pulled-back radicals and descends their range equality. The
conclusion is equality on all test schemes, including nonreduced ones.

The provenance is internal composition of published local dynamics, dynamic
Levi structure, radical construction and radical uniqueness results. The
unchanged target's source correspondence is Conrad, *Reductive group
schemes* (2014), Corollary 5.2.5, first assertion, printed/PDF p.153, as
recorded in [the target statement](UnipotentRadicalStatement.md).
The implemented proof discharges both the local dynamic presentation and
dynamic relative Levi inputs. It imposes no additional hypothesis on the
base, the parabolic or a global cocharacter, and changes neither the target
statement nor its imports.
