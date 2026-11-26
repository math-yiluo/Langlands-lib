# Relative-rank induction for orbit finiteness and Fourier injectivity

`RationalExactRankFourierInjectivityStatement` is the zero case of
Waldspurger VIII.1 (2) for the actual Fourier family on groups of a fixed
relative semisimple rank. The rank is the dimension of the span of relative
roots for a maximal split torus. The strict bound increases by one exactly
when the injectivity assertion for that rank is added.

`rationalPlancherelRankInduction` combines two supplied local rank steps.
The finiteness step takes orbit finiteness and Fourier injectivity in
strictly smaller rank. It adds the finiteness assertion for the current
rank, using the Library's existing proof in rank zero. The injectivity step
takes finiteness through the current rank and injectivity in strictly smaller
rank. The two results at every bound give global orbit finiteness and
global Fourier injectivity. This is the order of Waldspurger's induction
in VIII.1.3 and VIII.5. Its analytic steps are the two displayed premises
of the induction theorem.

`RationalSemistandardLeviFourierData.fourier_injective_of_lowerRank` applies
the strict bound to the Fourier transform used on a proper semistandard
Levi in VIII.2.1. The rank comparison and the chosen Levi's actual field,
group, torus, compact and Haar data give the local zero case for that
transform. This permits detection of a vanishing proper constant term
once its Fourier family has been shown to vanish.

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, 2003, VIII.1–VIII.2.1 and VIII.5, printed
pp. 320–322 and 331–332.
[DOI 10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082).
